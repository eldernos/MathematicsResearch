# Even-order characters, periodic Lambert weights and q-digamma reflection values

Phase 21, Tracks B1–B4. Fix an integer radix $b\ge2$. As in Phase 20, $D_N(x)=D_N(x;b)$ is the extreme discrepancy of $\{b^nx\}$, $0\le n<N$, and $K_b=\{z:D_N(z)\to1\}$ is the numerical translation kernel. For an integer sequence $a$ put $F_b(a)=\sum_{n\ge1}a(n)b^{-n}$,

```math
S_a(X)=\#\{1\le n\le X:\ a(n)\ne0\},\qquad A_a(X)=\sum_{n\le X}|a(n)| .
```

For a weight $w:\mathbb Z_{\ge1}\to\mathbb C$ write $(1*w)(n)=\sum_{d\mid n}w(d)$ and

```math
\mathcal L_w(b)=\sum_{m\ge1}\frac{w(m)}{b^m-1}=\sum_{n\ge1}(1*w)(n)\,b^{-n},\qquad
A_{r,M}(b)=\mathcal L_{\mathbf 1_{r\bmod M}}(b)=\sum_{m\equiv r\ (M)}\frac1{b^m-1}.
```

For a Dirichlet character $\chi$ modulo $q$ put $c_\chi=1*\chi$ and $L_\chi(b)=\mathcal L_\chi(b)$; for nonreal $\chi$ this is a complex number. Further notation: $\operatorname{ord}\chi$ is the order of $\chi$, $\lambda(q)$ the Carmichael function (the exponent of $(\mathbb Z/q)^\times$), $P_2(q)$ the Sylow 2-subgroup of $(\mathbb Z/q)^\times$, and $Z_\chi=\{a\in(\mathbb Z/q)^\times:\chi(a)=-1\}$ the *killing set* of $\chi$.

**Summary of conclusions.**

| Result | Evidence |
| --- | --- |
| B1. Every character $\chi$ of even order $h$ (either parity, primitive or not) has $S_{c_\chi}(X)\sim C_\chi X(\log X)^{-1/h}$; the exponent $1/h$ is sharp and comes from $e=1$ alone (Theorem 1.3) | Paper proof; external inputs Shiu, Wirsing, PNT in progressions |
| B1. $\sum_{n\le X}\lvert c_\chi(n)\rvert\asymp X(\log X)^{\kappa_h-1}$ with $\kappa_h=\frac2h\cot\frac\pi{2h}$ ($h$ even): linear mass fails for every nonreal $\chi$ (Proposition 1.4) | Paper proof (Wirsing); finite data |
| B1. Every integer-valued finite combination of dilated even-order divisor sums lies in $K_b$ in **every** radix, with $1-D_N\ll(\log\log N)/(\log N)^{1/H}$ (Theorem 1.5) | Paper proof from Phase 20 log-mass transfer |
| B1. If $\varphi(q)$ is a power of 2, every zero-sum integer combination of the $A_{r,q}(b)$ lies in $K_b$; in particular $A_{1,5}(b)-A_{2,5}(b)\in K_b$, answering Phase 20 open question 2 (Corollary 1.6) | Paper proof; finite data |
| B2. Mod $2^k$: exact identity $2^{k-1}A_{r,2^k}-E_{\rm odd}=\sum_{\chi\ne\chi_0}\overline{\chi(r)}L_\chi$ with integer coefficients; membership in $K_b$ for all $b$; binary transfer $D_N(A_{r,2^k}(2))-D_N(E_{\rm odd}(2))\to0$ for every fixed $k$ (Theorems 2.2–2.3) | Paper proof; exact cyclotomic check mod 16, 32 |
| B2. The $2^{k-1}-1$ nonprincipal characters mod $2^k$ have only $2k-3$ distinct supports, each independent of $k$ (Lemma 2.1, Proposition 2.4) | Paper proof; exact check to $10^5$ |
| B3. For every odd periodic integer weight, primes $p\equiv-1\pmod M$ kill $1*w$ at odd exponents, so $\mathcal L_w(b)\in K_b$ for all $b$ (Theorem 3.2); for $w=\mathbf 1_r-\mathbf 1_{-r}$ the support exponent is exactly $1/\lambda(M)$ | Paper proof (elementary + characters); finite data |
| B3. Sector dichotomy: $S_{1*w}(X)=o(X)$ **iff** every gcd stratum of $w$ sums to zero on the cosets of the Sylow 2-subgroup; otherwise the support has positive lower density (Theorem 3.4) | Paper proof; exact Fourier check on 210 weights |
| B4. $[\psi_q(r/M)-\psi_q(1-r/M)]/\log q=+\bigl(A_{r,M}(b)-A_{M-r,M}(b)\bigr)$ at $q=b^{-M}$, hence in $K_b$ for all $b,M,r$ (Theorem 4.1, Corollary 4.2) | Paper proof; 50-digit check; the membership is also implied by Phase 20 Theorem 7 (Eisenstein case) |
| B4. Every even-sector integer linear form in $\psi_q(r/M)$, divided by $\log q$, lies in $K_b$ (Corollary 4.3) | Paper proof; 50-digit check |
| B4. Two-character divisor sums $\psi*\varphi$ with $\varphi\bar\psi$ of even order, including the non-modular case $\psi\varphi$ even, e.g. $\sum_m\chi_{-3}(m)\,b^m/(b^{2m}+1)\in K_b$ (Theorem 4.4) | Paper proof; finite data |
| B4. $q$-polygamma reflection values: dense support and polynomial coefficients, the method fails; $q$-Gauss multiplication yields no new constants | Paper proof of the failure mechanism; finite data |

No digit statement is made about any number outside $K_b$. Where the sparse-support method stops (odd-order characters, the complementary sector, $q$-polygamma) nothing is inferred about normality or non-normality.

## 0. The transfer input

**Transfer (T).** Let $a$ be integer-valued with $S_a(X)\le C_1X(\log X)^{-\kappa}$ and $A_a(X)\le C_2X(\log X)^\beta$ for $X\ge3$, where $\kappa>0$ and $\beta\ge0$. Then for every $b\ge2$ and all large $N$,

```math
1-D_N(F_b(a))=\sup_x\bigl|D_N(x+F_b(a))-D_N(x)\bigr|\le(2\kappa+\beta+o(1))\,C_1\,\frac{\log_b\log N}{(\log N)^{\kappa}} .
```

*Source.* Phase 20 [coefficient-transfer Theorem 1.7](../phase20/coefficient-transfer.md#14-larger-mass) gives $1-D_N\le\rho(2\log_b(1/\rho)+\log_b\mu_N+O(1))$ with $\rho=(1+S_a(N-1))/N$ and $\mu_N=\max(1,\widehat A(2N)/N)\ll(\log N)^\beta$; the function $\rho\mapsto\rho\log(1/\rho)$ increases on $(0,1/e)$, so the upper bound for $\rho$ may be inserted. This is [Corollary 2 of the theta note](../phase20/theta-and-modular.md#1-coefficient-transfer) with the constant made explicit. The equality with the translation supremum is `SharpTranslation.sharp_translation_isGreatest`.

*Lean status.* For the linear-mass case $\beta=0$, both the finite and asymptotic transfer theorems are kernel-checked (`CoefficientTransfer.finite_sparse_mass_transfer`, `linear_mass_sparse_tendsto_one`). Proposition 1.4 shows that $\beta>0$ is unavoidable for nonreal characters; the finite and qualitative logarithmic-mass transfer theorems for every integer $\gamma \ge 0$ (`GeneralMassTransfer.finite_log_mass_transfer`, `log_mass_sparse_tendsto_one`, `log_mass_sparse_preserves_discrepancy`) are kernel-verified in Lean 4, while the sharper explicit rate $(2\kappa+\beta+o(1))\,C_1(\log_b\log N)/(\log N)^\kappa$ uses the Phase 20 paper Theorem 1.7.

## 1. B1 — characters of even order

### 1.1 Local values

**Lemma 1.1.** Let $\chi$ be a character modulo $q$, $p$ a prime and $e\ge1$. Then $c_\chi$ is multiplicative and:

1. if $p\mid q$, then $c_\chi(p^e)=1$;
2. if $\chi(p)=1$, then $c_\chi(p^e)=e+1$;
3. if $\chi(p)=\zeta\ne1$ has exact order $d\ge2$, then $c_\chi(p^e)=(1-\zeta^{e+1})/(1-\zeta)$, which vanishes exactly when $d\mid e+1$.

In particular $\chi(p)=-1$ gives $c_\chi(p^e)=0$ for every odd $e$, and $c_\chi(n)=0$ exactly when some prime $p\nmid q$ with $p^e\Vert n$ has $d_p\ge2$ and $d_p\mid e+1$.

*Proof.* $c_\chi(p^e)=\sum_{j=0}^e\chi(p)^j$ is a geometric sum. ∎

So for a character of order $h\ge4$, primes with $\chi(p)$ a primitive $h$-th root of unity do produce zeros, but only at exponents $e\equiv-1\pmod h$, $e\ge h-1\ge3$; a prime with $\chi(p)$ of order 3 (possible when $3\mid h$) produces zeros at $e\equiv2\pmod3$. All of these sit at exponents $e\ge2$.

### 1.2 The killing set

**Lemma 1.2.** Let $\operatorname{ord}\chi=h$.

1. If $h$ is even, $Z_\chi$ is a coset of $\ker\chi$ with $\varphi(q)/h$ elements. If $h$ is odd, $Z_\chi=\emptyset$, since $-1\notin\mu_h$.
2. For even $h$ the primes with $\chi(p)=-1$ have natural density $1/h$ among the primes, and $\sum_{p\le x,\ \chi(p)=-1}1/p=\frac1h\log\log x+c_\chi+o(1)$ for a constant $c_\chi\in\mathbb R$.
3. If $\chi$ is induced by a primitive $\chi^*$ modulo $q^*\mid q$, then $\operatorname{ord}\chi=\operatorname{ord}\chi^*$ and $\chi(p)=\chi^*(p)$ for $p\nmid q$. The two killing sets of primes differ by at most the finitely many primes dividing $q$, which changes neither density nor the harmonic sum by more than $O(1)$.

*Proof.* $\chi:(\mathbb Z/q)^\times\to\mu_h$ is a surjective homomorphism, and the fibre over $-1$ is a coset of the kernel. Item 2 is the prime number theorem for the fixed modulus $q$ (respectively Mertens' theorem in progressions, a consequence of $L(1,\chi')\ne0$ for all characters $\chi'$ modulo $q$). Item 3 is immediate. ∎

### 1.3 Support count with sharp exponent

**Theorem 1.3.** Let $\chi$ have even order $h$. Then

```math
S_{c_\chi}(X)\sim C_\chi\,\frac{X}{(\log X)^{1/h}}\qquad(X\to\infty)
```

for a constant $C_\chi>0$. The exponent $1/h$ is determined by the primes of $Z_\chi$ at exponent $e=1$; the zeros of Lemma 1.1(3) at exponents $e\ge2$ change only $C_\chi$. If instead $h$ is odd, every squarefree $n$ coprime to $q$ has $c_\chi(n)\ne0$, so $S_{c_\chi}$ has lower density at least $\frac6{\pi^2}\prod_{p\mid q}\frac p{p+1}$.

*Proof.* The support indicator $g=\mathbf 1[c_\chi\ne0]$ is multiplicative (a product of local factors vanishes exactly when one factor does), takes values in $\{0,1\}$, and $g(p)=0$ exactly for the primes of $Z_\chi$.

- *Upper bound.* Shiu's theorem (J. Reine Angew. Math. **313** (1980), 161–170, Theorem 1, with modulus $1$ and $y=x$) applies to nonnegative multiplicative $g$ with $g(p^e)\le A_1^e$ and $g(n)\ll_\varepsilon n^\varepsilon$, and gives $\sum_{n\le x}g(n)\ll\frac x{\log x}\exp\bigl(\sum_{p\le x}g(p)/p\bigr)$. By Lemma 1.2(2) the exponent is $(1-\frac1h)\log\log x+O(1)$, so the sum is $\ll x(\log x)^{-1/h}$.
- *Asymptotic.* Wirsing's theorem (Math. Ann. **143** (1961), 75–102, Satz 1) in its prime-number-theorem form requires $g\ge0$ multiplicative, $\sum_{p\le x}g(p)\sim\tau x/\log x$ with $\tau>0$, and $g(p^\nu)\le AB^\nu$ with $B<2$. Here $\tau=1-1/h$ by the PNT in progressions, and $g\le1$. It gives $\sum_{n\le x}g(n)\sim\frac{e^{-\gamma\tau}}{\Gamma(\tau)}\frac x{\log x}\prod_{p\le x}\sum_{\nu\ge0}g(p^\nu)p^{-\nu}$. The local factor is $1+1/p+O(p^{-2})$ for $p\notin Z_\chi$ and $1+O(p^{-2})$ for $p\in Z_\chi$, whatever the higher zeros are. Mertens' theorem in progressions makes the product $\sim C'(\log x)^{\tau}$.
- *Odd order.* For squarefree $n$ coprime to $q$, $c_\chi(n)=\prod_{p\mid n}(1+\chi(p))$ and $1+\chi(p)\ne0$ because $\chi(p)\ne-1$. ∎

The lower bound alone follows immediately from the same Wirsing input: squarefree $n$ coprime to $q$ whose prime factors avoid $Z_\chi$ lie in the support, and Wirsing counts them as $\asymp X(\log X)^{-1/h}$.

### 1.4 Mass

**Proposition 1.4.** For every Dirichlet character $\chi$ of order $h\ge1$, $|c_\chi(n)|\le\tau(n)$, so $A_{c_\chi}(X)\le X(\log X+1)$. More precisely,

```math
\sum_{n\le X}|c_\chi(n)|\sim C'_\chi\,X(\log X)^{\kappa_h-1},\qquad
\kappa_h=\frac1h\sum_{j=0}^{h-1}\bigl|1+e^{2\pi ij/h}\bigr|=
\begin{cases}\frac2h\cot\frac\pi{2h},&h\text{ even},\\[2pt] \frac2h\csc\frac\pi{2h},&h\text{ odd}.\end{cases}
```

The values are $\kappa_1=2$, $\kappa_2=1$, $\kappa_3=4/3$, $\kappa_4=(1+\sqrt2)/2=1.2071$, $\kappa_6=(2+\sqrt3)/3=1.2440$, $\kappa_8=1.2568$, $\kappa_{12}=1.2660$, and $\kappa_h\to4/\pi$. Hence $A_{c_\chi}(X)=O(X)$ holds **exactly for nonprincipal real characters** ($h=2$); for $\chi_0$ ($h=1$) the mass is $\asymp X\log X$, and for every nonreal $\chi$ ($h\ge3$) the mass grows like $X(\log X)^{\kappa_h-1}$ with $\kappa_h>1$.

*Proof.* Apply Wirsing to $f=|c_\chi|$: $f(p)=|1+\chi(p)|$ for $p\nmid q$, each value $\zeta\in\mu_h$ is taken by $\chi(p)$ on a set of primes of density $1/h$, and $f(p^\nu)\le\nu+1\le2(3/2)^\nu$. The closed forms are the sums $\sum_j|\cos(\pi j/h)|$. For $h=1$, $\kappa_1=2$. For $h\ge3$ the triangle inequality is strict, $\sum_{j=0}^{h-1}|1+\zeta^j|>|\sum_{j=0}^{h-1}(1+\zeta^j)|=h$, so $\kappa_h>1$. ∎

These are the Eisenstein values in the table of Phase 20 [Theorem 7](../phase20/theta-and-modular.md#3-weight-one-modular-forms). The script finds $A(X)/(X(\log X)^{0.2071})=0.9945,\ 0.9965,\ 0.9963$ at $X=10^3,10^4,10^5$ for the quartic character modulo 5, while $A(X)/X$ itself rises from $1.484$ to $1.653$. The consequence is the one stated in §0: complex characters require the log-mass transfer.

### 1.5 The finite-coefficient character transfer

**Theorem 1.5.** Let $J\ge1$, let $\chi_1,\dots,\chi_J$ be Dirichlet characters of even orders $h_1,\dots,h_J$ (any moduli, any parities), let $d_1,\dots,d_J\ge1$ and $\lambda_1,\dots,\lambda_J\in\mathbb C$, and put

```math
a(n)=\sum_{j=1}^J\lambda_j\,c_{\chi_j}(n/d_j),\qquad c(x)=0\text{ for }x\notin\mathbb Z .
```

Suppose $a(n)\in\mathbb Z$ for every $n\ge1$. Let $H=\max_jh_j$ and $\Lambda=\sum_j|\lambda_j|$. Then:

1. $\operatorname{supp}a\subseteq\bigcup_jd_j\operatorname{supp}c_{\chi_j}$, so $S_a(X)\le\sum_jS_{c_{\chi_j}}(X/d_j)\ll X(\log X)^{-1/H}$;
2. $|a(n)|\le\Lambda\tau(n)$, so $A_a(X)\le\Lambda X(\log X+1)$;
3. for **every** integer radix $b\ge2$, $F_b(a)\in K_b$ and

```math
1-D_N(F_b(a))=\sup_x\bigl|D_N(x+F_b(a))-D_N(x)\bigr|\ll_{a,b}\frac{\log\log N}{(\log N)^{1/H}} .
```

*Proof.* If every $c_{\chi_j}(n/d_j)$ vanishes then $a(n)=0$, and Theorem 1.3 bounds each set. Also $|c_\chi(m)|\le\tau(m)\le\tau(n)$ for $m\mid n$. Apply (T) with $\kappa=1/H$ and $\beta=1$. Integrality of $a$ is what makes every head $\sum_{n\le N}a(n)b^{N-n}$ an integer. ∎

*Remarks.*

1. **Integrality is a condition on the weight.** $a=1*w$ with $w(m)=\sum_j\lambda_j\chi_j(m/d_j)$, and $a$ is integer-valued if and only if $w=\mu*a$ is. So Theorem 1.5 concerns integer-valued periodic weights whose Fourier expansion (on each gcd stratum) uses only even-order characters. Section 3.3 characterizes them exactly.
2. **The $\lambda_j$ need not be rational.** For example $\mathbf 1_1-\mathbf 1_2\pmod5=\frac12\chi_5+\frac{1+i}4\chi+\frac{1-i}4\bar\chi$, with $\chi_5$ quadratic (even) and $\chi$ quartic (odd), $\chi(2)=i$.
3. **Linear mass is not needed and usually false** (Proposition 1.4). The exponent $\beta$ only enters the window length $L=O(\log\log N)$.
4. **Sharpness.** The exponent $1/H$ is attained for single-stratum weights (Proposition 3.6).
5. **What Phase 20 had.** Phase 20's Theorem E1.3 is the case $H=2$. Its remark that nonreal characters are out of reach is corrected here: nonreal characters of **even** order are covered; the obstruction is **odd** order (Theorem 3.4).

### 1.6 Moduli whose unit group is a 2-group; Phase 20 open question 2

**Corollary 1.6.** Let $q\ge3$ with $\varphi(q)$ a power of 2, equivalently $q=2^aF_1\cdots F_s$ with distinct Fermat primes $F_i$. For every $b\ge2$ and every integer-valued $w$ on the reduced classes modulo $q$ with $\sum_xw(x)=0$, $\mathcal L_w(b)\in K_b$. In particular, for all $r,s$ coprime to $q$,

```math
A_{r,q}(b)-A_{s,q}(b)\in K_b,\qquad \varphi(q)A_{r,q}(b)-E_q(b)\in K_b ,
```

with $E_q(b)=\sum_{(m,q)=1}1/(b^m-1)$, and for $r\not\equiv s$ the support exponent is exactly $1/\lambda(q)$. For $q=5$:

```math
A_{1,5}(b)-A_{2,5}(b)\in K_b\quad\text{for every }b\ge2,\qquad 1-D_N\ll_b\frac{\log\log N}{(\log N)^{1/4}} .
```

This answers [Phase 20 classical-transfers, open question 2](../phase20/classical-transfers.md#5-open-questions) affirmatively.

*Proof.* Every nonprincipal character of a 2-group has order $2^j\ge2$, and the zero sum removes $\chi_0$; apply Theorem 1.5. For the exponent: the elements of maximal order $\lambda(q)$ generate the character group (write it as $C_{n_1}\times\dots\times C_{n_s}$ with $n_s=\lambda$; if $e_s$ generates the last factor, $e_s+e_i$ has order $\lambda$ and $e_i=(e_s+e_i)-e_s$), so they cannot all lie in the proper subgroup $\{\chi:\chi(r)=\chi(s)\}$. Proposition 3.6 then gives the lower bound. ∎

The script finds support densities $0.574,\ 0.553,\ 0.529$ at $X=10^3,10^4,10^5$ for $1*(\mathbf 1_1-\mathbf 1_2)\pmod5$; for the antisymmetric weight $\mathbf 1_1-\mathbf 1_4\pmod5$ it finds $1-D_{1500}=0.92$ in base 2 (§3). These are finite data.

### 1.7 Relation to Phase 20

- **Real characters** (order 2, either parity): Phase 20 Theorem E1.3 and D3.1(2). Linear mass holds, so these cases are kernel-checked through `finite_sparse_mass_transfer`.
- **Odd characters of any order:** the weight-one Eisenstein series $E_1^{1,\varphi}$, $\varphi$ odd, have coefficients $c_\varphi(n)$, and Phase 20 [Theorem 7](../phase20/theta-and-modular.md#3-weight-one-modular-forms) already observed that $\varphi(-1)=-1$ forces even order. Integer combinations of odd characters are therefore within Phase 20 Theorem 7 once the rational constant term is discarded.
- **New here:** even characters of even order $h\ge4$ (for example the order-6 characters modulo 13 and the even quartic characters modulo 16). For them $\sum c_\chi(n)q^n$ is not a holomorphic weight-one form, since weight-one Eisenstein series need $\psi\varphi$ odd. Also new: the direct support-union argument, which needs no denominators; the exact exponent; and the classification of §3.3.

### 1.8 Finite data

Prime density of $Z_\chi$ up to $2\cdot10^5$, parity, and $S(N)/N$ next to $S(N)(\log N)^{1/h}/N$ at $N=10^3,10^4,10^5,2\cdot10^5$:

| character | $h$ | parity | density of $\chi(p)=-1$ | $S/N$ and $S(\log N)^{1/h}/N$ |
| --- | --- | --- | --- | --- |
| mod 5, quartic | 4 | odd | 0.2493 | 0.719/1.166, 0.662/1.154, 0.622/1.146, 0.612/1.144 |
| mod 13, order 12 | 12 | odd | 0.0830 | 0.884/1.038, 0.861/1.036, 0.844/1.035, 0.840/1.034 |
| mod 13, order 6 | 6 | even | 0.1668 | 0.644/0.889, 0.614/0.889, 0.590/0.886, 0.584/0.886 |
| mod 16, $\chi_{0,1}$ | 4 | even | 0.2496 | 0.683/1.107, 0.629/1.097, 0.591/1.089, 0.582/1.087 |
| mod 16, $\chi_{1,1}$ | 4 | odd | 0.2500 | 0.788/1.277, 0.725/1.263, 0.680/1.253, 0.669/1.250 |
| mod 7, order 6 | 6 | odd | 0.1665 | 0.701/0.967, 0.665/0.963, 0.638/0.959, 0.632/0.958 |
| mod 8, $\chi_{-8}$ | 2 | odd | 0.5017 | 0.377/0.991, 0.315/0.955, 0.275/0.934, 0.266/0.929 |

The second ratio is nearly constant, consistent with Theorem 1.3, but data in this range cannot determine an exponent. Galois-conjugate characters have identical supports (checked to $2\cdot10^4$; this is Lemma 1.1, since vanishing is Galois invariant). For odd order, the cubic characters modulo 7, 9 and 13 have no zero among squarefree $n\le2000$ coprime to the modulus.

## 2. B2 — moduli $2^k$

### 2.1 The characters modulo $2^k$

For $k\ge3$, $(\mathbb Z/2^k)^\times=\langle-1\rangle\times\langle5\rangle\cong C_2\times C_{2^{k-2}}$. Write $m\equiv(-1)^a5^e$ and $\zeta=e^{2\pi i/2^{k-2}}$. The characters are

```math
\chi_{s,t}(m)=(-1)^{as}\,\zeta^{te},\qquad s\in\{0,1\},\ t\in\mathbb Z/2^{k-2},
```

with parity $\chi_{s,t}(-1)=(-1)^s$. Every nonprincipal character has order $2^j$ with $1\le j\le k-2$. For $k=2$ the only nonprincipal character is $\chi_{-4}$.

**Lemma 2.1.** Let $k\ge3$.

1. There are $3$ characters of order 2 and $2^j$ characters of order $2^j$ for $2\le j\le k-2$.
2. A character of order $2^j\ge4$ has conductor $2^{j+2}$. The real ones have conductor 4 ($\chi_{-4}$) or 8 ($\chi_8$, $\chi_{-8}$).
3. The Galois orbits are: three of order 2, and two of each order $2^j\ge4$ (one even, one odd).
4. $\operatorname{supp}c_\chi$ depends only on the Galois orbit of $\chi$ and equals $\operatorname{supp}c_{\chi^*}$ for the primitive $\chi^*$. Hence the $2^{k-1}-1$ nonprincipal characters modulo $2^k$ have exactly $2k-3$ distinct supports, and each of them is independent of $k$.

*Proof.* (1) $C_2\times C_{2^{k-2}}$ has $2^{j+1}$ elements of order dividing $2^j$ ($1\le j\le k-2$). (2) An order-$2^j$ character is trivial on $5^{2^j}$, which generates the classes $\equiv1\pmod{2^{j+2}}$, and nontrivial on $5^{2^{j-1}}\equiv1\pmod{2^{j+1}}$. (3) $t\mapsto ut$ with $u$ odd preserves $s$ and the order; in each parity slice the $2^{j-1}$ characters of order $2^j$ form one orbit. (4) Vanishing of $c_\chi(n)\in\mathbb Z[\zeta]$ is Galois invariant, and $c_\chi(2^e)=c_{\chi^*}(2^e)=1$. Distinct orbits have distinct kernels, hence distinct killing cosets (a coset $Z$ determines its subgroup as $\{xy^{-1}:x,y\in Z\}$), and a prime in one killing set but not the other lies in exactly one support. The count is $3+2(k-3)=2k-3$. ∎

### 2.2 The exact identity

**Theorem 2.2.** For $k\ge2$ and odd $r$, orthogonality $\sum_\chi\overline{\chi(r)}\chi(m)=2^{k-1}\mathbf 1[m\equiv r\ (2^k)]$ (odd $m$) gives

```math
a_{k,r}(n):=2^{k-1}\tau_{r,2^k}(n)-\tau_{\rm odd}(n)=\sum_{\chi\ne\chi_0}\overline{\chi(r)}\,c_\chi(n)\in\mathbb Z,
\qquad \tau_{r,q}(n)=\#\{d\mid n:\ d\equiv r\ (q)\},
```

hence for every $b\ge2$

```math
Z_{k,r}(b):=2^{k-1}A_{r,2^k}(b)-E_{\rm odd}(b)=F_b(a_{k,r})=\sum_{\chi\ne\chi_0}\overline{\chi(r)}\,L_\chi(b),
```

where $E_{\rm odd}(b)=\sum_{m\text{ odd}}1/(b^m-1)$. The right side is real although its terms are not. Class differences are integer-weight series as well: $A_{r,2^k}(b)-A_{s,2^k}(b)=\mathcal L_{\mathbf 1_r-\mathbf 1_s}(b)=2^{1-k}\sum_{\chi\ne\chi_0}(\overline{\chi(r)}-\overline{\chi(s)})L_\chi(b)$.

The script checks orthogonality and the coefficient identity exactly in $\mathbb Z[\zeta_4]$ (mod 16) and $\mathbb Z[\zeta_8]$ (mod 32), for all odd $r$ and $n\le1500$, by reduction modulo the cyclotomic polynomial.

### 2.3 Kernel membership and the binary transfer

Put $H_2=H_3=2$ and $H_k=2^{k-2}$ for $k\ge3$; the two definitions agree at $k=3$.

**Theorem 2.3.** Let $k\ge2$ and let $r,s$ be odd.

1. **Every radix.** For every $b\ge2$, $Z_{k,r}(b)\in K_b$ and $A_{r,2^k}(b)-A_{s,2^k}(b)\in K_b$, with $1-D_N\ll_{k,b}(\log\log N)/(\log N)^{1/H_k}$. The support exponent $1/H_k$ is exact for $Z_{k,r}(b)$, and also for $A_{r,2^k}(b)-A_{s,2^k}(b)$ whenever $r\not\equiv s\pmod{2^k}$. Consequently $|D_N(A_{r,2^k}(b))-D_N(A_{s,2^k}(b))|\to0$ in every radix.
2. **Radices $b=2^t$ with $t\mid k-1$, in particular $b=2$.**

```math
\bigl|D_N(A_{r,2^k}(b))-D_N(E_{\rm odd}(b))\bigr|\le\frac{k-1}{tN}+\bigl(1-D_N(Z_{k,r}(b))\bigr)\ll_k\frac{\log\log N}{(\log N)^{1/H_k}},
```

so $D_N(A_{r,2^k}(2))-D_N(E_{\rm odd}(2))\to0$ for every fixed $k\ge2$ and odd $r$.
3. **Other even radices.** Let $j=\lceil(k-1)/v_2(b)\rceil$ and $c=b^j/2^{k-1}\in\mathbb Z$. Then $|D_N(A_{r,2^k}(b))-D_N(c\,E_{\rm odd}(b))|\le j/N+(1-D_N(cZ_{k,r}(b)))\to0$. The comparison is with $c\,E_{\rm odd}(b)$, and $c$ is a power of $b$ only in case 2.
4. **Odd radices.** Only item 1 and $|D_N(2^{k-1}A_{r,2^k}(b))-D_N(E_{\rm odd}(b))|\to0$ are claimed. Multiplication by $2^{k-1}$ is not a radix shift; the Phase 20 base-6 example shows that $D_N(2y)$ and $D_N(y)$ can have different limits.

*Proof.* (1) The weights $2^{k-1}\mathbf 1_r-\mathbf 1_{\rm odd}$ and $\mathbf 1_r-\mathbf 1_s$ live on the units and have zero sum over $(\mathbb Z/2^k)^\times=P_2(2^k)$; all nonprincipal characters have 2-power order. Theorem 1.5 applies. All nonprincipal characters occur in $a_{k,r}$ with coefficient $\overline{\chi(r)}\neq0$, and for $r\not\equiv s\pmod{2^k}$ the maximal-order elements of $\widehat{(\mathbb Z/2^k)^\times}$ generate the group so at least one character of order $H_k$ satisfies $\chi(r)\ne\chi(s)$ (as in Corollary 1.6); Proposition 3.6 then gives exactness for both. (2) $b^{(k-1)/t}A_r=E_{\rm odd}+Z$; combine `radixDiscrepancy_mul_pow_sub_le` ($|D_N(b^jx)-D_N(x)|\le j/N$) with sharp translation. (3) $b^jA_r=c(E_{\rm odd}+Z)$, and $K_b$ is a group. ∎

**Corrections to the brief.** "In fact any power of 2" requires $t\mid k-1$: in base 4 with $k=4$ one gets $D_N(A_{r,16}(4))\approx D_N(2E_{\rm odd}(4))$, and the script shows $D_{1200}(E_{\rm odd}(4))=0.211$ against $D_{1200}(2E_{\rm odd}(4))=0.327$. Also, $A_{r,2^k}(b)-A_{s,2^k}(b)\in K_b$ holds in **every** radix, not only in even ones, because the class difference is itself an integer weight with zero sum.

### 2.4 Explicit dependence on $k$

**Proposition 2.4.** For $j\ge1$ let $T_j(N)$ be the number of $n\le N$ in the union of the supports of the characters of order $2^j$ modulo $2^{j+2}$ ($T_1$ uses $\chi_{-4},\chi_8,\chi_{-8}$). Then for $k\ge3$, all odd $1\le r<2^k$, all $b\ge2$ and all large $N$ (in particular once $N\ge 2^k$ and $\rho_k\le 1/e$, which holds for every fixed $k$ as $N\to\infty$):

```math
S_{a_{k,r}}(N)\le\sum_{j=1}^{k-2}T_j(N),\qquad A_{a_{k,r}}(X)\le X\Bigl(\frac{2^{k-1}}r+\frac32+\log X\Bigr),
```

```math
1-D_N(Z_{k,r}(b))\le\rho_k\Bigl(2\log_b\frac1{\rho_k}+\log_b\Bigl(\frac{2^k}r+2\log(4N)+3\Bigr)+4\Bigr),\qquad
\rho_k=\frac{1+\sum_{j\le k-2}T_j(N)}N .
```

The dependence on $k$ enters only through the number $k-2$ of sets $T_j$, the weakest exponent $2^{-(k-2)}$, and the additive term $\log_b(2^k/r)\le k\log_b2$. **There is no factor $2^{k-1}$ from the character count**: the per-character triangle inequality of Phase 20 E1.3 is replaced by the support union, and the $2^{k-1}-1$ characters have only $2k-3$ supports (Lemma 2.1). Each $T_j(N)\sim C_jN(\log N)^{-2^{-j}}$ for fixed $j$ by Theorem 1.3.

*Proof.* Lemma 2.1 and Theorem 1.5(1) give the support bound. For the mass, $\sum_{n\le X}\tau_{r,2^k}(n)\le X\bigl(\frac1r+\frac{1+\log X}{2^k}\bigr)$ and $\sum_{n\le X}\tau_{\rm odd}(n)\le X(1+\frac12\log X)$. Insert into Theorem 1.7 of the coefficient-transfer note. ∎

**Uniformity hypothesis (U).** If $T_j(N)\le C_*N(\log N)^{-2^{-j}}$ with an absolute $C_*$ whenever $2^{j+2}\le(\log N)^{1/2}$, then

```math
1-D_N(Z_{k,r}(b))\ll k\,(\log N)^{-2^{2-k}}\bigl(k+\log_2\log N\bigr),
```

which is below 1 only for $k\le\log_2\log\log N-\log_2\log\log\log N+O(1)$. Hypothesis (U) follows from the Shiu bound once Mertens' theorem for primes $\equiv a\pmod{2^m}$ holds with an error uniform in $2^m\le(\log N)^{1/2}$. That is in the Siegel–Walfisz range, and for 2-power moduli the constants are effective, because no real primitive character has 2-power conductor larger than 8. We use (U) only to describe the trade-off in [classical-barriers.md](classical-barriers.md); no theorem below depends on it.

### 2.5 Finite data

Support densities $S_{a_{k,r}}(N)/N$ at $N=10^5$: $0.2403$ ($k=2$), $0.5680$ ($k=3$), $0.8829$ ($k=4$, $r=1$), $0.9829$ ($k=5$), $0.9992$ ($k=6$), $1.0000$ ($k\ge7$). The support of every $a_{k,r}$ lies inside the union of the $2k-3$ character supports (exact to $10^5$). For fixed $k$ the density tends to 0 only like $(\log N)^{-2^{2-k}}$, which is invisible at this range.

Certified binary discrepancies at $N=2000$ ($D_{2000}(E_{\rm odd})=0.1147$):

| $k$ | $r$ | $D_N(A_{r,2^k})$ | $1-D_N(Z_{k,r})$ | $\lvert D_N(A_r)-D_N(E_{\rm odd})\rvert$ |
| --- | --- | --- | --- | --- |
| 2 | 1 | 0.1013 | 0.6680 | 0.0134 |
| 3 | 3 | 0.1131 | 0.9688 | 0.0016 |
| 4 | 3 | 0.2007 | 0.9397 | 0.0860 |
| 4 | 15 | 0.3305 | 0.9467 | 0.2157 |
| 5 | 1 | 0.6049 | 0.9448 | 0.4902 |
| 6 | 63 | 0.7856 | 0.8926 | 0.6708 |

Every row (14 in the script) satisfies the inequality of Theorem 2.3(2); at this $N$ the bound is far from small. For $k\ge5$ the classes $A_{1,2^k}$ and $A_{2^k-1,2^k}$ are visibly concentrated, a finite-range effect explained in [classical-barriers.md §1.2](classical-barriers.md#12-what-a-growing-k-would-need).

## 3. B3 — periodic weights

### 3.1 Antisymmetric weights

**Proposition 3.1.** Let $M\ge3$, $\gcd(r,M)=1$ and $w=\mathbf 1_r-\mathbf 1_{-r}$. Then

```math
\varphi(M)\,\widehat w(\chi)=\overline{\chi(r)}-\overline{\chi(-r)}=(1-\chi(-1))\,\overline{\chi(r)},
```

so only odd characters occur, each with coefficient $2\overline{\chi(r)}/\varphi(M)\ne0$. Moreover:

1. every odd character has even order, because $-1$ lies in its image;
2. the largest order of an odd character modulo $M$ is exactly $\lambda(M)$;
3. $(1*w)(n)=\tau_{r,M}(n)-\tau_{-r,M}(n)$ is integer-valued **without** multiplying by $\varphi(M)$; the factor $1/\varphi(M)$ belongs to the expansion, not to the sequence.

*Proof of 2.* The even characters form an index-2 subgroup of the character group. The elements of maximal order $\lambda(M)$ generate the group (§1.6), so one of them is odd. ∎

The script checks the coefficient formula exactly in $\mathbb Z[\zeta_{\lambda(M)}]$ for $M=3,\dots,10,12,13,16$, and items 1 and 2 for every $3\le M\le300$.

### 3.2 Odd periodic weights: an elementary vanishing theorem

**Theorem 3.2.** Let $w:\mathbb Z\to\mathbb Z$ be $M$-periodic ($M\ge3$) and odd, $w(-m)=-w(m)$.

1. $w(0)=0$, and $w(M/2)=0$ when $M$ is even.
2. If $p$ is a prime with $w(px)=-w(x)$ for all $x$ (in particular every prime $p\equiv-1\pmod M$), then $(1*w)(n)=0$ whenever $v_p(n)$ is odd. This holds for all divisors, coprime to $M$ or not.
3. Hence $S_{1*w}(X)\ll X(\log X)^{-1/\varphi(M)}$, $A_{1*w}(X)\le\max|w|\cdot X(\log X+1)$, and $\mathcal L_w(b)\in K_b$ for **every** $b\ge2$.

*Proof.* (2) Write $n=p^em$ with $p\nmid m$. The divisors are $p^id'$ with $d'\mid m$ and $0\le i\le e$, and $w(p^id')=(-1)^iw(d')$. So $(1*w)(n)=\sum_{d'\mid m}w(d')\sum_{i=0}^e(-1)^i=0$ for odd $e$. (3) Shiu's bound with the primes $\equiv-1\pmod M$ (density $1/\varphi(M)$), then (T). ∎

This argument uses no characters. It is the mechanism behind the lacunarity of weight-one Eisenstein series.

**Lemma 3.3 (gcd strata).** For an $M$-periodic $w$ and $g\mid M$ let $\tilde w_g(x)=w(gx)\,\mathbf 1[\gcd(x,M/g)=1]$, which is $M/g$-periodic. Then

```math
(1*w)(n)=\sum_{g\mid\gcd(n,M)}(1*\tilde w_g)(n/g),\qquad \mathcal L_w(b)=\sum_{g\mid M}\mathcal L_{\tilde w_g}(b^g).
```

If $w$ is odd, every stratum is odd on $(\mathbb Z/(M/g))^\times$, and the strata with $M/g\in\{1,2\}$ vanish.

*Proof.* $\gcd(gd',M)=g$ exactly when $\gcd(d',M/g)=1$. ∎

**Exact exponent.** By the character expansion of each stratum and Proposition 3.6 below (which covers both single-stratum and multi-stratum even-sector weights), the support exponent of any nonzero odd weight $w$ is $1/H$, with $H$ the largest order of a character occurring in some stratum. Here $H\le\lambda(M)$, and $H=\lambda(M)$ for $w=\mathbf 1_r-\mathbf 1_{-r}$ with $\gcd(r,M)=1$ (Proposition 3.1):

```math
S_{1*(\mathbf 1_r-\mathbf 1_{-r})}(X)\asymp\frac X{(\log X)^{1/\lambda(M)}} .
```

The brief asked whether the exponent sharpens to the 2-part of $\lambda(M)$ or to the largest even order. It does neither: it equals $1/\lambda(M)$ exactly. The elementary Theorem 3.2 gives the weaker $1/\varphi(M)$.

### 3.3 The sector dichotomy

For $m\ge1$ the odd-order characters modulo $m$ are exactly the characters trivial on $P_2(m)$ (for $m=1$, $(\mathbb Z/1)^\times=\{0\}$ has size $1$, so the single coset condition for $g=M$ is $w(0)=0$; for $m=2$, $(\mathbb Z/2)^\times=\{1\}$ is also trivial and $P_2(m)$ is all of it).

**Definition.** An integer-valued $M$-periodic $w$ lies in the **even-order sector** $\mathcal E_M$ if for every $g\mid M$ and every coset $C$ of $P_2(M/g)$ in $(\mathbb Z/(M/g))^\times$

```math
\sum_{x\in C}w(gx)=0 .
```

The **complementary projection** $w^{(O)}$ replaces each value $w(gx)$, $x$ a unit modulo $M/g$, by its average over $xP_2(M/g)$, and $w^{(E)}=w-w^{(O)}$.

**Theorem 3.4.** For an integer-valued $M$-periodic $w$ the following are equivalent:

1. $S_{1*w}(X)=o(X)$;
2. $w\in\mathcal E_M$;
3. every stratum $\tilde w_g$ has $\widehat{\tilde w_g}(\chi)=0$ for every character $\chi$ modulo $M/g$ of odd order (including $\chi_0$).

If they hold and $w\ne0$, then $S_{1*w}(X)\asymp X(\log X)^{-1/H}$, where $H$ (an even number) is the largest order of a character occurring in any stratum, $A_{1*w}(X)\ll X\log X$, and $\mathcal L_w(b)\in K_b$ for every $b\ge2$ with $1-D_N\ll(\log\log N)/(\log N)^{1/H}$. If they fail, then $\liminf S_{1*w}(X)/X>0$. The sparse-support method then says nothing about $\mathcal L_w(b)$, and no membership or non-membership in $K_b$ is claimed.

*Proof.* (2)⇔(3): a function on a finite abelian group $G$ has vanishing Fourier coefficients at all characters of $G/P_2$ exactly when its push-forward to $G/P_2$ vanishes, that is, when it sums to zero on every coset. A character of $G/P_2$ has odd order; conversely an odd-order $\chi$ satisfies $\chi(g)=1$ on $P_2$, since the order of $\chi(g)$ divides both an odd number and a power of 2. (3)⇒(1): Theorem 1.5 applied to the strata (Lemma 3.3), with the matching lower bound from Proposition 3.6. (1)⇒(2): take $g_0$ minimal under divisibility with $\tilde w_{g_0}^{(O)}\ne0$. For $n'$ coprime to $M$,

```math
(1*w)(g_0n')=(1*\tilde w^{(E)}_{g_0})(n')+(1*\tilde w^{(O)}_{g_0})(n')+\sum_{g\mid g_0,\ g<g_0}(1*\tilde w_g)(g_0n'/g).
```

The first term and the last sum vanish outside a set of density zero: $|P_2|\,\tilde w^{(E)}_{g_0}$ is an integer weight in the even sector, the lower strata lie in the sector by minimality, and $n'\mapsto g_0n'/g$ is injective. Lemma 3.5 shows that the middle term is nonzero on a set of $n'$ of positive lower density. ∎

**Lemma 3.5 (complementary nonvanishing).** Let $u\ne0$ be a rational-valued function on $(\mathbb Z/m)^\times$ that is constant on the cosets of $P_2(m)$, extended by 0, and let $m\mid M'$. Then $\{n\text{ coprime to }M':(1*u)(n)\ne0\}$ has positive lower density.

*Proof.* Let $X_u$ be the set of (odd-order) characters with $\hat u(\chi)\ne0$, and put $R=|X_u|\ge1$. For squarefree $n$ coprime to $m$,

```math
(1*u)(n)=\sum_{\chi\in X_u}\hat u(\chi)\prod_{p\mid n}(1+\chi(p)),
```

and every factor $1+\chi(p)$ is nonzero because $\chi$ has odd order. Since $1+\chi(1)=2$ is constant, $\chi(h)=(1+\chi(h))-\frac12(1+\chi(1))$ lies in the linear span of $\{\chi\mapsto 1+\chi(h):h\in(\mathbb Z/m)^\times\}$. By linear independence of characters, the degree-1 functions $f_i(\chi)=1+\chi(h_i)$ for suitable $h_1,\dots,h_R\in(\mathbb Z/m)^\times$ form a basis of $\mathbb C^{X_u}$. By Dirichlet's theorem choose $R$ pairwise distinct primes $q_1,\dots,q_R\nmid M'$ with $q_i\equiv h_i\pmod m$, and put $\mathcal P=\{q_1,\dots,q_R\}$. For every squarefree $n\le X/\max_i q_i$ coprime to $M'\mathcal P$, the vector $v(\chi)=\hat u(\chi)c_\chi(n)$ has no zero entry, so $(1*u)(nq_i)=\sum_\chi v(\chi)(1+\chi(h_i))\ne0$ for some $i=i(n)\in\{1,\dots,R\}$. Because $\gcd(n,\mathcal P)=1$ and the $q_i$ are distinct primes, the map $n\mapsto nq_{i(n)}$ is injective into $\{k\le X:\gcd(k,M')=1,\ (1*u)(k)\ne0\}$. Hence the set has lower density at least $(\max_i q_i)^{-1}$ times the density of squarefree integers coprime to $M'\mathcal P$. ∎

**Proposition 3.6 (sharp exponent).** Let $w\ne0$ be an integer-valued $M$-periodic weight in $\mathcal E_M$, and let $H$ be the largest order of a character occurring in any gcd stratum $\tilde w_g$ ($g\mid M$). Then $S_{1*w}(X)\gg X(\log X)^{-1/H}$.

*Proof.* Choose $g_0\mid M$ minimal under divisibility among all strata carrying a character of maximal order $H$, and fix such a $\chi^*$ modulo $M/g_0$, with Galois orbit $O=\{\chi^{*u}:u\in(\mathbb Z/H)^\times\}$. Since $\tilde w_{g_0}$ is rational-valued, $\widehat{\tilde w_{g_0}}(\chi^{*u})=\sigma_u(\widehat{\tilde w_{g_0}}(\chi^*))$, so every member of $O$ occurs in $\tilde w_{g_0}$. For $n'$ coprime to $M$, Lemma 3.3 gives

```math
(1*w)(g_0n')=(1*\tilde w_{g_0})(n')+\sum_{g\mid g_0,\ g<g_0}(1*\tilde w_g)\bigl((g_0/g)n'\bigr).
```

Lift $\chi^*$ and every occurring character $\chi$ (mod $M/g$) across all $g\mid g_0$ to characters modulo $M$; on integers coprime to $M$, $c_\chi$ agrees with $c_{\chi^{\rm lift}}$ (and for $g<g_0$, $c_\chi((g_0/g)n')=c_\chi(g_0/g)c_{\chi^{\rm lift}}(n')$). Let $\mathcal X_{\rm other}$ be the finite set of all these lifted characters modulo $M$ outside the lifted orbit $O$. By minimality of $g_0$, every character from a proper divisor $g<g_0$ has even order $<H$, so no lower stratum contributes to $O$.

- *Killing the other characters.* For every $\chi\in\mathcal X_{\rm other}$, $Z_\chi\not\subseteq Z_{\chi^*}$ in $(\mathbb Z/M)^\times$: either $|Z_\chi|=\varphi(M)/\operatorname{ord}\chi>|Z_{\chi^*}|$, or $\operatorname{ord}\chi=H$ with $\chi\notin O$, where $Z_\chi=Z_{\chi^*}$ would force equal kernels $\{xy^{-1}:x,y\in Z_\chi\}$ and hence $\chi\in O$. Pick pairwise distinct primes $p_\chi\nmid M$ with classes in $Z_\chi\setminus Z_{\chi^*}$ and put $m_0=\prod_{\chi\in\mathcal X_{\rm other}}p_\chi$. Then $c_\chi(m_0n)=0$ whenever $\gcd(n,Mm_0)=1$ and $\chi\in\mathcal X_{\rm other}$, while $c_{\chi^*}(m_0)\ne0$.
- *Rotating the trace.* If $H=2$, set $Q=1$; for every squarefree $n$ coprime to $Mm_0$ with all prime factors outside $Z_{\chi^*}$, $(1*w)(g_0m_0n)=\widehat{\tilde w_{g_0}}(\chi^*)c_{\chi^*}(m_0)c_{\chi^*}(n)\ne0$. If $H\ge4$, choose pairwise distinct primes $q_1,\dots,q_{\varphi(H)-1}\nmid Mm_0$ with $\chi^*(q_l)=\zeta_H$ (by Dirichlet's theorem), and put $Q=\prod_{l=1}^{\varphi(H)-1}q_l$. For every squarefree $n\le X/(g_0m_0Q)$ coprime to $Mm_0Q$ with all prime factors outside $Z_{\chi^*}$, the factors $m_0$, $n$, and $q_1\cdots q_i$ ($0\le i<\varphi(H)$) are pairwise coprime and squarefree, so every $\chi\in\mathcal X_{\rm other}$ still satisfies $p_\chi\Vert m_0nq_1\cdots q_i$ and vanishes, while
  $$(1*w)(g_0m_0nq_1\cdots q_i)=\operatorname{Tr}_{\mathbb Q(\zeta_H)/\mathbb Q}\!\bigl(\beta\gamma(1+\zeta_H)^i\bigr)$$
  with $\beta=\widehat{\tilde w_{g_0}}(\chi^*)c_{\chi^*}(m_0)\ne0$ and $\gamma=c_{\chi^*}(n)\ne0$. Since $\mathbb Q(1+\zeta_H)=\mathbb Q(\zeta_H)$, the powers $(1+\zeta_H)^i$, $0\le i<\varphi(H)$, form a $\mathbb Q$-basis (checked exactly for $H=4,6,8,10,12,16$). The trace form is nondegenerate, so some $i=i(n)\in\{0,\dots,\varphi(H)-1\}$ makes $(1*w)(g_0m_0nq_1\cdots q_{i(n)})\ne0$.

Because $\gcd(n,Q)=1$ and the $q_l$ are distinct primes, $n\mapsto g_0m_0nq_1\cdots q_{i(n)}$ is injective on $n\le X/(g_0m_0Q)$ (the $Q$-smooth part recovers $i(n)$ and hence $n$), and Wirsing's theorem counts the admissible squarefree $n$ coprime to $Mm_0Q$ outside $Z_{\chi^*}$ as $\gg X(\log X)^{-1/H}$. ∎

### 3.4 Examples, and where the method stops

| $M$ | $\varphi$ | $\lambda$ | $\lvert P_2\rvert$ | dim of $\mathcal E$ on units | largest odd-character order |
| --- | --- | --- | --- | --- | --- |
| 5 | 4 | 4 | 4 | 3 | 4 |
| 7 | 6 | 6 | 2 | 3 | 6 |
| 9 | 6 | 6 | 2 | 3 | 6 |
| 13 | 12 | 12 | 4 | 9 | 12 |
| 15 | 8 | 4 | 8 | 7 | 4 |
| 16 | 8 | 4 | 8 | 7 | 4 |
| 17 | 16 | 16 | 16 | 15 | 16 |
| 21 | 12 | 6 | 4 | 9 | 6 |

The dimension of the even sector on the units is $\varphi(M)-\varphi(M)/|P_2(M)|$. When $|P_2(M)|=2$, that is $M=4$, $p^a$ or $2p^a$ with $p\equiv3\pmod4$, the even sector on the units is exactly the space of odd weights. When $\varphi(M)$ is a power of 2 it consists of all zero-sum weights.

**Odd-order characters.** For the cubic character $\chi$ modulo 7, $1+\chi(p)\in\{2,e^{i\pi/3},e^{-i\pi/3}\}$, so for squarefree $n$ coprime to 7, $c_\chi(n)=2^ae^{i\pi(b-c)/3}$ and

```math
(1*(\chi+\bar\chi))(n)=2^{a+1}\cos\frac{\pi(b-c)}3\ne0 .
```

Here $\chi+\bar\chi=2\cdot\mathbf 1_{\{1,6\}}-\mathbf 1_{\{2,5\}}-\mathbf 1_{\{3,4\}}$. The script confirms nonvanishing on every squarefree $n\le2\cdot10^5$ prime to 7; the support density is $0.7504$. The sparse-support method genuinely stops at even order.

Support densities at $X=10^3,10^4,10^5$ (parities of the characters used: e = even, o = odd):

| weight | sector | densities |
| --- | --- | --- |
| mod 5, $\mathbf 1_1-\mathbf 1_2$ | even, $H=4$, e+o | 0.5740, 0.5533, 0.5288 |
| mod 13, $\chi_6+\bar\chi_6$ | even, $H=6$, e only | 0.5600, 0.5284, 0.5045 |
| mod 16, $\mathbf 1_{\{1,15\}}-\mathbf 1_{\{7,9\}}$ | even, $H=4$, e only | 0.5660, 0.5159, 0.4788 |
| mod 7, $\mathbf 1_1-\mathbf 1_6$ | even, $H=6$, o only | 0.6440, 0.6040, 0.5739 |
| mod 7, $\mathbf 1_1-\mathbf 1_2$ | mixed | 0.5660, 0.5662, 0.5680 |
| mod 7, $\mathbf 1_{\{1,6\}}-\mathbf 1_{\{2,5\}}$ | complementary | 0.5040, 0.5008, 0.5004 |
| mod 13, $\mathbf 1_{P_2}-\mathbf 1_{2P_2}$ | complementary | 0.5040, 0.5068, 0.5075 |

The rows "mod 13, $\chi_6+\bar\chi_6$" and "mod 16, $\mathbf 1_{\{1,15\}}-\mathbf 1_{\{7,9\}}$" use only even characters of order 6 and 4. They are not weight-one modular, so they lie outside Phase 20 Theorem 7.

### 3.5 Reduction modulo $K_b$ in even radices

**Corollary 3.7.** Let $w$ be integer-valued and $M$-periodic, and let $2^s=\max_{g\mid M}|P_2(M/g)|$. Then $2^s\bigl(\mathcal L_w(b)-\mathcal L_{w^{(O)}}(b)\bigr)\in K_b$ for every $b\ge2$, and $\mathcal L_w(b)-\mathcal L_{w^{(O)}}(b)\in K_b$ for every even $b$.

*Proof.* $2^sw^{(E)}$ is an integer weight in $\mathcal E_M$. In even radices $2^s\mid b^s$, and $K_b$ is a $\mathbb Z[1/b]$-module. ∎

So in even radices, modulo $K_b$, every periodic Lambert constant reduces to its odd-order projection. That projection is exactly what the method cannot decide.

## 4. B4 — $q$-digamma and other $q$-special functions

### 4.1 Conventions

For $0<q<1$ and $x>0$ (Jackson; Gasper–Rahman, *Basic Hypergeometric Series*, §1.10),

```math
\Gamma_q(x)=(1-q)^{1-x}\frac{(q;q)_\infty}{(q^x;q)_\infty},\qquad
\psi_q(x)=\frac{\Gamma_q'(x)}{\Gamma_q(x)}=-\log(1-q)+\log q\sum_{k\ge0}\frac{q^{k+x}}{1-q^{k+x}}=-\log(1-q)+\log q\sum_{j\ge1}\frac{q^{jx}}{1-q^j}.
```

The script evaluates $\psi_q$ in three independent ways: by numerically differentiating $\log\Gamma_q$ from the product at 150-digit precision, from the first series, and from the Lambert form. The three agree to $6.2\cdot10^{-77}$ in all 14 test cases.

### 4.2 The reflection identity and its sign

**Theorem 4.1.** Let $b\ge2$, $M\ge2$, $1\le r<M$ and $q=b^{-M}$. Then

```math
\frac{\psi_q(r/M)-\psi_q(1-r/M)}{\log q}
=\sum_{k\ge0}\frac{1}{b^{kM+r}-1}-\sum_{k\ge0}\frac1{b^{kM+M-r}-1}
=A_{r,M}(b)-A_{M-r,M}(b)=\sum_{n\ge1}\bigl(\tau_{r,M}(n)-\tau_{-r,M}(n)\bigr)b^{-n}.
```

The sign is $+$.

*Proof.* The $-\log(1-q)$ terms cancel. Termwise, $q^{k+r/M}=b^{-(kM+r)}$ and $q^{k+1-r/M}=b^{-(kM+M-r)}$, and $q^a/(1-q^a)=1/(b^{Ma}-1)$. Everything converges absolutely. ∎

*Sign check.* $\log q=-M\log b<0$. For $2r<M$ each term of $A_{r,M}$ exceeds the matching term of $A_{M-r,M}$, so the right side is positive and $\psi_q(r/M)<\psi_q(1-r/M)$. This agrees with $\psi_q'(x)=(\log q)^2\sum_k q^{k+x}/(1-q^{k+x})^2>0$. Over 14 cases ($b\in\{2,3,5,7,10\}$, including $\gcd(r,M)>1$ and $2r=M$) the identity holds to $1.6\cdot10^{-73}$, against the 50-digit target.

### 4.3 Membership in $K_b$

**Corollary 4.2.** For every $b\ge2$, $M\ge2$ and $1\le r<M$,

```math
X_{b,M,r}:=\frac{\psi_{b^{-M}}(r/M)-\psi_{b^{-M}}(1-r/M)}{\log(b^{-M})}\in K_b .
```

Let $g=\gcd(r,M)$, $M'=M/g$, and $r'=r/g$. If $2r=M$ then $X_{b,M,r}=0$ (with empty support). If $g>1$, then $X_{b,M,r}=X_{b^g,M',r'}$ (the same $q$), and in base $b$ the coefficient sequence of $X_{b,M,r}$ is the $g$-dilate of that of $A_{r',M'}(b^g)-A_{-r',M'}(b^g)$. Whenever $2r\ne M$ (so $M'\ge3$), the rate is $1-D_N(X_{b,M,r})\ll_{b,M,r}(\log\log N)/(\log N)^{1/\lambda(M')}$, the support exponent $1/\lambda(M')$ is exact, and $\sup_x|D_N(x+X_{b,M,r})-D_N(x)|=1-D_N(X_{b,M,r})$.

*Proof.* $w=\mathbf 1_r-\mathbf 1_{-r}\pmod M$ is odd, so Theorem 3.2 applies. Its only nonzero stratum is $g$, with $\tilde w_g=\mathbf 1_{r'}-\mathbf 1_{-r'}\pmod{M'}$ and $\gcd(r',M')=1$; dilation by $g$ does not change the exponent. For $2r\ne M$, $M'\ge3$ and Propositions 3.1 and 3.6 apply. ∎

### 4.4 Linear forms in $q$-digamma values

**Corollary 4.3.** Let $c_1,\dots,c_{M-1}\in\mathbb Z$, let $w$ be the $M$-periodic weight with $w(r)=c_r$ and $w(0)=0$, and suppose $w\in\mathcal E_M$. Then $\sum_rc_r=0$ and, for $q=b^{-M}$,

```math
\frac1{\log q}\sum_{r=1}^{M-1}c_r\,\psi_q(r/M)=\sum_{r=1}^{M-1}c_r\,A_{r,M}(b)=\mathcal L_w(b)\in K_b .
```

If $w\notin\mathcal E_M$, the coefficient support has positive lower density and the method is silent.

*Proof.* Summing the coset conditions over all cosets and all strata gives $\sum_rc_r=0$, so the $-\log(1-q)$ terms cancel in the series definition of $\psi_q(r/M)$. Termwise $q^{k+r/M}/(1-q^{k+r/M})=1/(b^{kM+r}-1)$, giving $\sum c_rA_{r,M}(b)=\mathcal L_w(b)$, and Theorem 3.4 applies. ∎

*Examples.*

- $M=5$: every integer zero-sum combination, e.g. $[\psi_q(1/5)-\psi_q(2/5)]/\log q$, or $[2\psi_q(1/5)-\psi_q(2/5)-\psi_q(4/5)]/\log q$ (checked to 50 digits at $q=3^{-5}$).
- $M=p$ prime with $p\equiv3\pmod4$: exactly the reflection-odd combinations.
- $M=17$: all zero-sum combinations.

### 4.5 The $q$-cotangent, theta functions and Eisenstein series

The reflection formula $\Gamma_q(x)\Gamma_q(1-x)=(1-q)(q;q)_\infty^2/\bigl((q^x;q)_\infty(q^{1-x};q)_\infty\bigr)$ and Jacobi's triple product $(z;q)_\infty(q/z;q)_\infty(q;q)_\infty=\sum_{n\in\mathbb Z}(-1)^nq^{n(n-1)/2}z^n$ give

```math
\psi_q(x)-\psi_q(1-x)=-\frac{d}{dx}\log\sum_{n\in\mathbb Z}(-1)^nq^{n(n-1)/2+nx},
```

the $q$-analogue of $\psi(1-x)-\psi(x)=\pi\cot\pi x$. All three were checked to 50 digits at $q=2^{-5}$. Thus $X_{b,M,r}$ is a value of the logarithmic derivative of a Jacobi theta function at a torsion point. Equivalently, $\sum_n(\tau_{r,M}(n)-\tau_{-r,M}(n))Q^n$ is, up to a rational constant, a weight-one Eisenstein series on $\Gamma_1(M)$: its odd-character expansion consists of $E_1^{1,\varphi}$ and their oldforms, as in Diamond–Shurman, Theorem 4.8.1. **Corollary 4.2 is therefore also a consequence of Phase 20 Theorem 7 (Eisenstein case)** after the constant term is discarded. Track B4 adds the elementary proof, the exact exponent $1/\lambda(M')$, and the explicit $q$-digamma normalization and sign.

### 4.6 The $q$-Gauss multiplication formula: no new constants

$n\psi_q(nx)=n\log[n]_q+\sum_{j=0}^{n-1}\psi_{q^n}(x+j/n)$ with $[n]_q=(1-q^n)/(1-q)$ (checked to 50 digits). Take $q=b^{-M}$ and $x=r/(nM)$. After normalization the formula is equivalent to the partition relation

```math
A_{r,M}(b)=\sum_{j=0}^{n-1}A_{r+jM,\,nM}(b),
```

which the script checks exactly. Multiplication produces no constants outside the residue-class family.

### 4.7 $q$-polygamma: the method fails

For $j\ge1$, $\psi_q^{(j)}(x)=(\log q)^{j+1}\sum_{k\ge1}k^jq^{kx}/(1-q^k)$, and

```math
\frac{\psi_q^{(j)}(r/M)-\psi_q^{(j)}(1-r/M)}{(\log q)^{j+1}}=\sum_{n\ge1}s_j(n)b^{-n},\qquad s_j(n)=\sum_{m\mid n}\Bigl(\frac nm\Bigr)^j\bigl(\mathbf 1_r-\mathbf 1_{-r}\bigr)(m)
```

(checked to 40 digits for $j=1$). The coefficients are $(\mathrm{id}^j*w)(n)$, the weight-$(j+1)$ Eisenstein type. Two things break at once:

- **No local zeros (and dense support).** For a character $\chi$, $(\mathrm{id}^j*\chi)(p^e)=\sum_{i=0}^e\chi(p)^ip^{(e-i)j}$ has modulus at least $p^{ej}-\sum_{i=1}^ep^{(e-i)j}\ge 1>0$. For the combination $s_j=\mathrm{id}^j*(\mathbf 1_r-\mathbf 1_{-r})$, the dominant-divisor bound below (using $m=1$ when $r\equiv\pm1$, or a least prime $q_0\equiv r\pmod M$ for general $r$) gives positive support density: all coefficients are nonzero up to $10^5$ for $(M,r)=(5,1)$, and the densities are $0.875\to0.902$ for $(5,2)$ and $0.659\to0.747$ for $(12,5)$, increasing.
- **Polynomial size.** $A(X)\ll X^{j+1}$, and when $r\equiv\pm1$ and $n\ge2$ the term $m=1$ dominates: $|s_j(n)|\ge n^j-\tau(n)(n/P^-(n))^j$, where $P^-(n)$ is the least prime factor of $n$. For $(M,r)=(5,1)$ and $j=1$ the binary width density $W(X)/X$ is $8.94$, $12.28$, $15.61$ at $X=10^3,10^4,10^5$.

This is the Phase 20 §4 footprint obstruction in a stronger form: there is not even lacunarity. Nothing is claimed about these values.

### 4.8 Two-character divisor sums

**Theorem 4.4.** Let $\psi$, $\varphi$ be Dirichlet characters and $\sigma_{\psi,\varphi}(n)=\sum_{d\mid n}\psi(n/d)\varphi(d)$, so that

```math
\sum_{n\ge1}\sigma_{\psi,\varphi}(n)b^{-n}=\sum_{m\ge1}\varphi(m)\,\Psi(b^{-m}),\qquad\Psi(x)=\sum_{k\ge1}\psi(k)x^k .
```

At $p\nmid$ both moduli, $\sigma(p^e)=\psi(p)^e\sum_{i=0}^e\omega(p)^i$ with $\omega=\varphi\bar\psi$. If $\omega$ has even order $h$, then $\sigma(p^e)=0$ for odd $e$ whenever $\omega(p)=-1$, and $S_\sigma(X)\ll X(\log X)^{-1/h}$. Every integer-valued finite combination of dilates of such $\sigma$, possibly with different pairs $(\psi,\varphi)$ but all $\omega$ of even order, lies in $K_b$ for every $b\ge2$, with $1-D_N\ll(\log\log N)/(\log N)^{1/H}$.

*Proof.* As for Theorems 1.3 and 1.5, with $|\sigma|\le\tau$. ∎

When $\psi\varphi$ is odd these are the weight-one Eisenstein series of Phase 20 Theorem 7. When $\psi\varphi$ is **even** there is no holomorphic weight-one form, and the constants are new. Example: $\psi=\chi_{-4}$, $\varphi=\chi_{-3}$, $\psi\varphi=\omega=\chi_{12}$ (even, real), $\Psi(x)=x/(1+x^2)$:

```math
\sum_{m\ge1}\chi_{-3}(m)\frac{b^m}{b^{2m}+1}=\sum_{m\equiv1\,(3)}\frac{b^m}{b^{2m}+1}-\sum_{m\equiv2\,(3)}\frac{b^m}{b^{2m}+1}\in K_b\qquad(b\ge2),
```

with $1-D_N\ll(\log\log N)/\sqrt{\log N}$. The coefficients vanish at $p\equiv5,7\pmod{12}$ to odd powers (exact to $10^5$), and the support densities are $0.383$, $0.319$, $0.279$ at $10^3,10^4,10^5$. The generating identity holds to 50 digits for $b=2,3,10$, and $1-D_{1500}=0.828$ in base 2.

### 4.9 Other $q$-series

- **Rogers–Ramanujan** $G(q),H(q)$: partition-type coefficients of size $\exp(c\sqrt n)$, dense; the method fails, as for $P_b$ in Phase 20.
- **Borwein cubic theta functions:** $a(q)=\Theta_{m^2+mn+n^2}$ is Phase 20 Theorem A; $q^{-1/3}c(q)$ (or $c(b^{-3})$) is a shifted lattice (Theorem A, §2.2); $b(q)=(q;q)_\infty^3/(q^3;q^3)_\infty$ is an integral weight-one form (Theorem B). Nothing new.
- **Jacobi elliptic functions** at rational arguments: their Lambert parts, such as $\sum_nq^n/(1+q^{2n})\cos(2nv)$, reduce after Galois symmetrization to two-character and periodic sums already covered. The prefactors $\pi/(2K)$ are transcendental and destroy radix integrality, and nothing is claimed about the elliptic-function values themselves.

### 4.10 New members of $K_b$ from Track B

Genuinely beyond Phase 20:

1. Lambert sums of even characters of even order $\ge4$ and their integer combinations, for example the mod 13 order-6 trace weight and the mod 16 weight $\mathbf 1_{\{1,15\}}-\mathbf 1_{\{7,9\}}$.
2. All zero-sum residue-class combinations for moduli with $\varphi(q)$ a power of 2, in every radix, including Phase 20 open question 2.
3. The mod $2^k$ family (Theorem 2.3).
4. Two-character sums with $\psi\varphi$ even.

Already implied by Phase 20 Theorem 7 but now explicit, with exact exponents: the $q$-digamma reflection values and the odd periodic weights.

## 5. Verification

```sh
python -B scripts/phase21_characters_classical.py
```

Standard library only; 20–40 s depending on machine load; exits 0 after 374,840 assertions (the count includes Track E). For Track B it checks:

- **Lemma 1.1** exactly in $\mathbb Z[\zeta_L]$ at 14,652 prime powers. The support criterion equals exact nonvanishing of $c_\chi(n)$ for 88,000 pairs ($n\le2000$, all characters modulo 5, 7, 8, 9, 12, 13, 16).
- **Densities:** the density of $\chi(p)=-1$ is within $0.02$ of $1/h$ up to $2\cdot10^5$; support tables; Galois-invariance of supports.
- **Mass:** the closed forms of $\kappa_h$; the mass growth for $h\ge4$.
- **Odd order:** nonvanishing for odd-order characters and for $\chi+\bar\chi$ modulo 7.
- **Sectors:** the coset criterion equals vanishing of all odd-order Fourier coefficients (210 weights). Even-sector supports lie inside the union of character supports (to $10^5$). The basis property of $(1+\zeta_H)^i$.
- **Mod $2^k$:** orders, conductors, character counts; exact orthogonality and the coefficient identity mod 16 and 32; $2k-3$ distinct $k$-independent supports for $k\le8$; certified binary discrepancies and the transfer inequality.
- **Odd weights:** the vanishing at $p\equiv-1$; the gcd-strata identity for 42 random odd weights; certified discrepancies of $A_{r,M}(b)-A_{-r,M}(b)$ for 8 pairs $(M,r)$ in bases 2, 3, 5, 10, cross-checked against the exact Lambert sums.
- **$q$-functions:** the 50-digit $q$-digamma, reflection, theta and multiplication checks; $q$-polygamma; two-character sums.

All discrepancies come from certified integer enclosures of $b^Kx$ and are accurate to $10^{-9}$. Ratios and densities are finite data only.

## 6. Recommended Lean finite cores

The Phase 21 Lean modules `NormalityChecker/GeneralMassTransfer.lean`, `NormalityChecker/AntisymmetricLambert.lean`, and `NormalityChecker/ClassicalBarriers.lean` have been built with zero warnings and kernel-replayed (`leanchecker`), formalizing the logarithmic-mass transfer (`log_mass_sparse_tendsto_one`), odd-periodic divisor-involution cancellation (`dirichletOneConv_eq_zero_of_odd_padicVal`), the exact `q`-digamma reflection identity (`qDigamma_reflection_eq_residueLambert`, `qDigamma_reflection_eq_dirichletSeries`), the anti-multiplicative vanishing theorem (`dirichletOneConv_eq_zero_of_antiMul`), the gcd-strata decomposition (`dirichletOneConv_strata`), local vanishing at `-1` (`sum_pow_eq_zero_of_eq_neg_one`), and support-union bounds (`supportCount_combo_le`). Remaining schematic candidate signatures for future formalization:

```lean
namespace NormalityChecker.Phase21Characters
open Finset

/-- (1 * w)(n) = ∑_{d ∣ n} w d (same as `AntisymmetricLambert.dirichletOneConv`). -/
def oneStar (w : ℕ → ℤ) (n : ℕ) : ℤ := ∑ d ∈ n.divisors, w d

/-- Theorem 3.2(2), multiplier form: a prime acting by −1 on `w` kills odd exponents.
Covers p ≡ −1 (mod M) for odd M-periodic w, coprime or not. -/
theorem oneStar_eq_zero_of_antiMul {w : ℕ → ℤ} {p m e : ℕ} (hp : p.Prime)
    (hanti : ∀ x, w (p * x) = - w x) (hm : ¬ p ∣ m) (he : Odd e) :
    oneStar w (p ^ e * m) = 0

/-- Lemma 1.1, local vanishing for a Dirichlet character with χ p = −1. -/
theorem sum_dirichletChar_prime_pow_eq_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p e : ℕ} (hχ : χ (p : ZMod q) = -1) (he : Odd e) :
    ∑ i ∈ range (e + 1), χ ((p : ZMod q) ^ i) = 0

/-- Lemma 3.3, gcd strata (finite divisor-sum algebra). -/
theorem oneStar_strata (M : ℕ) (hM : 0 < M) (w : ℕ → ℤ) (hper : ∀ m, w (m + M) = w m) (n : ℕ)
    (hn : 0 < n) :
    oneStar w n = ∑ g ∈ (Nat.gcd n M).divisors,
      oneStar (fun x => if Nat.Coprime x (M / g) then w (g * x) else 0) (n / g)

/-- Theorem 2.2, coefficientwise mod-2^k identity. Uses Mathlib orthogonality
(e.g. `DirichletCharacter.sum_char_inv_mul_char_eq`; check the current name). -/
theorem mod_two_pow_coeff_identity (k : ℕ) (hk : 2 ≤ k) (r : (ZMod (2 ^ k))ˣ) (n : ℕ) :
    ((2 ^ (k - 1) * ((n.divisors.filter fun d => (d : ZMod (2 ^ k)) = r).card : ℤ)
        - (n.divisors.filter Odd).card : ℤ) : ℂ) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (2 ^ k))).erase 1,
        χ ↑(r⁻¹) * ∑ d ∈ n.divisors, χ d

/-- Theorem 3.4 (2) ⇔ (3) on one stratum: coset sums over a subgroup `P` vanish iff all
characters trivial on `P` annihilate `w` (finite Fourier analysis on (ZMod m)ˣ). -/
theorem coset_sums_zero_iff {m : ℕ} (P : Subgroup (ZMod m)ˣ) (w : (ZMod m)ˣ → ℚ) :
    (∀ g, ∑ x ∈ (univ.filter fun x => x * g⁻¹ ∈ P), w x = 0) ↔
      ∀ χ : (ZMod m)ˣ →* ℂˣ, (∀ x ∈ P, χ x = 1) → ∑ x, (w x : ℂ) * ((χ x)⁻¹ : ℂˣ) = 0

/-- Theorem 1.5(1): the support of a finite combination lies in the union of supports. -/
theorem supportCount_combo_le {ι : Type*} (s : Finset ι) (c : ι → ℕ → ℂ) (coef : ι → ℂ)
    (a : ℕ → ℤ) (ha : ∀ n, (a n : ℂ) = ∑ i ∈ s, coef i * c i n) (X : ℕ) :
    CoefficientTransfer.supportCount a X ≤
      ∑ i ∈ s, ((Icc 1 X).filter fun n => c i n ≠ 0).card

end NormalityChecker.Phase21Characters
```

The analytic inputs (Shiu, Wirsing, the PNT in progressions) should enter as hypotheses on `supportCount`, exactly as `mod8_asymptotic_equivalence` treats the Phase 17 rate. Then `GeneralMassTransfer.log_mass_sparse_tendsto_one`, or the kernel-checked linear case for real characters, closes each membership statement.

## 7. Scope, external inputs and open questions

**Evidence.** Every theorem in this note is a paper proof. The script supplies exact finite checks of the algebraic identities and finite data for the asymptotic statements. No new Lean is part of this track.

**External inputs.**

- The prime number theorem and Mertens' theorem in progressions for fixed moduli (Montgomery–Vaughan, *Multiplicative Number Theory I*, Chapters 4 and 11).
- Shiu's theorem (1980, Theorem 1) for upper bounds.
- Wirsing's theorem (1961, Satz 1) for asymptotics and lower bounds.
- Phase 20 coefficient-transfer Theorem 1.7 (paper).
- For §4.5 only: the Eisenstein basis of $M_1(\Gamma_1(M))$ (Diamond–Shurman, Theorem 4.8.1).
- Hypothesis (U) of §2.4 is used only descriptively.

**Open questions.**

1. **Complementary sector.** Is $\mathcal L_{\chi+\bar\chi}(b)\in K_b$ for the cubic character modulo 7? More generally, is any Lambert sum with nonzero odd-order projection in $K_b$, or normal? The support has positive density, so a different method is needed.
2. **Leading constants** for complex characters, in the style of Phase 20's [lambert-leading-constant.md](../phase20/lambert-leading-constant.md). This needs isolation and width control: in base 2, $|c_\chi(n)|$ is not close to a power of 2 when $h\ge4$.
3. **Matching lower bounds** $1-D_N\gg(\log\log N)/(\log N)^{1/H}$ for Theorem 1.5.
4. **A proof of hypothesis (U)** with explicit constants.
