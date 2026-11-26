# Dyadic Stoneham polynomials: the 2-adic quadratic obstruction, a digit automaton for the leading mass and certificates through degree 120

Throughout, $b\ge3$ is an odd integer and $\alpha=\alpha_{b,2}=\sum_{j\ge1}2^{-j}b^{-2^j}$ is the positive-index Stoneham number. Write $v_2$ for the 2-adic order, $s=v_2(b^2-1)-1\ge2$, and $\lambda=\tfrac12\mathrm{Log}(b^{-2})=-\mathrm{Log}\,b\in4\mathbb Z_2$, where Log is the 2-adic (Iwasawa) logarithm, so $v_2(\lambda)=s$. In this note $\log_2$ always means the real base-2 logarithm. For the quadratic $A\alpha^2+B\alpha+C_0$ the Phase 14 upper-shell denominators are $q_k=2^{[k-v_2(2A)-s-v_2(k-\kappa)]_+}$ with

```math
\kappa=-\frac{2A+B+2AC}{2A\lambda},\qquad C=\lambda+\sum_{j\ge1}\bigl(\delta_j-\lambda\bigr),\qquad \delta_j=\frac{b^{-2^j}-1}{2^j}.
```

For $X^2-2X$ this is $\kappa_0=-C/\lambda$. For an integer $d\ge1$ and real $t$ let $M_d(t)\in\mathbb Z_2$ be the mass $\sum 2^{v_1+\cdots+v_d}$ of all $v\in\mathbb N^d$ with $\sum_i2^{-v_i}\le t$. On the shell $1\le t<2$ it is the leading coefficient of the shifted prefix of $\alpha^d$. [Quadratic denominators](../phase14/quadratic-denominators.md) · [Leading mass and its recurrence](../phase14/higher-degrees.md)

**Theorem A (the intercept as a 2-adic function; paper proofs).** As formal power series in $\lambda$, and as 2-adic analytic functions on $4\mathbb Z_2$,

```math
C(2\lambda)-2C(\lambda)=2\lambda+1-e^{2\lambda},\qquad
\kappa_0(2\lambda)-\kappa_0(\lambda)=\frac{e^{2\lambda}-1-2\lambda}{2\lambda}.
```

The functions $C$ and $\kappa_0$ are transcendental over $\mathbb C(\lambda,e^{\lambda/2^m}:m\ge0)$, in particular over $\mathbb Q(\lambda)$ and $\mathbb Q(\lambda,e^{2\lambda})$ (this is a function-field statement and does not decide the arithmetic of $\kappa_0(b)$ at any fixed integer radix $b$). The map $\lambda\mapsto\kappa_0(\lambda)$ is a bijective isometry of $4\mathbb Z_2$ onto $-1+4\mathbb Z_2$, with $\kappa_0'(\lambda)=1+O(2^{s+2})$. Consequently $|\kappa_0(b)-\kappa_0(b')|_2=|b-b'|_2$ whenever $b\equiv b'\pmod 4$. For Haar-almost every 2-adic parameter $\lambda\in4\mathbb Z_2$ one has $v_2(k-\kappa_0(\lambda))\le(1+\varepsilon)\log_2k$ for all large $k$. For each $c$, the parameters with $v_2(k-\kappa_0(\lambda))\ge k-c$ for infinitely many $k$ form a dense $G_\delta$ set of Hausdorff dimension zero; their union over $c\in\mathbb N$ has Hausdorff dimension zero, contains a dense $G_\delta$, and consists precisely of the parameters where the upper denominators stay bounded along a subsequence.

**Theorem A′ (fixed radix; paper proof and exact check).** For $X^2-2X$ define integers by $Z_1=2-2b^2$ and $Z_{k+1}=2+2b^{2^k}(Z_k-1)$. Then $q_k=2^{[2k-1-v_2(Z_k)]_+}$ unconditionally (also kernel-verified in [Phase16StonehamBounds.lean](../../NormalityChecker/Phase16StonehamBounds.lean)), and $v_2(Z_k)=k+s+v_2(k-\kappa_0)$ whenever $v_2(k-\kappa_0)<k-1+s$ (at or beyond that threshold both expressions are $\ge2k-1$, giving the same clipped denominator $q_k=1$; for example $b=5,k=3$ has $Z_3=-3061248$ with $v_2(Z_3)=9$ while $k+s+v_2(k-\kappa_0)=10$). Thus $(\alpha^2-2\alpha)/D$ is normal in base $b$ if and only if $2k-v_2(Z_k)\to\infty$. The functional equation of Theorem A is the base change $b\mapsto b^2$, under which this problem is equivalent to itself. It does not decide any fixed $b$. Section A.5 identifies where Mahler, q-difference, Schneider–Lang and two-logarithm methods each break down.

**Theorem B (leading masses; paper proofs and finite certificates).**

1. *Truncation and a digit automaton.* $M_d(t)$ is an ordinary integer for every real $t$. On $[1,2)$ it depends only on the binary expansion of $t$ truncated after its $d$-th digit 1. It is computed by a weighted automaton with $d(d+1)/2$ states, and its residue modulo $2^L$ depends only on the first $L$ binary digits of $t$.
2. *Certificates.* For every $3\le d\le120$, $M_d(t)\ne0$ for all $t\in[1,2)$. The exact maximal loss $\max_tv_2(M_d(t))$ and its location are listed in §B.2. Hence $P(\alpha)$ is normal in base $b$ for **every rational polynomial $P$ of degree 3 through 120**.
3. *Cyclic descent.* For an odd prime $p$, integers $r\ge1$, $e\ge1$ and $t\in[1,2)$, with $j$ chosen so that $y=2^jt/p^r\in[1,2)$,

   ```math
   M_{p^re}(t)\equiv 2^{ej}M_e(y)\pmod p .
   ```

   If $M_e$ never vanishes modulo $p$ on $[1,2)$, every degree $ep^r$ with $r\ge0$ has no zero cell. Finite automata over $\mathbb F_p$ certify this for $(e,p)\in\{(3,31),(3,127),(3,257),(3,337),(3,1801),(3,8191),(4,8191)\}$. Consequently every rational polynomial of degree $3\cdot31^r$, $3\cdot127^r$, $3\cdot257^r$, $3\cdot337^r$, $3\cdot1801^r$, $3\cdot8191^r$ or $4\cdot8191^r$ ($r\ge0$) has a normal value at $\alpha$. The case $e=1$ is the Phase 13 theorem for odd prime powers. For $e=2$ the reduced mass vanishes modulo every odd prime, so no prime certifies $d=2p^r$ this way.
4. *Least loss.* For every $t\in[1,2)$, $v_2(M_d(t))\ge v_2(d!)+F(d)$, where $F(d)$ is an explicit minimum over multisets. The identity $F(d)=\sum_{k=1}^d\lfloor\log_2k\rfloor$ is verified for $d\le299$. For $d\le120$ the least loss over the shell equals $v_2(d!)+\sum_{k\le d}\lfloor\log_2k\rfloor$. For $d\le64$ with $2^r-1\le d\le2^{r+1}-2$ it is attained exactly on $[2-2^{1-r},\,2-2^{-r})$, where a single orbit dominates, or on $[2-2^{1-r},2)$ when $d=2^r-1$. We conjecture the same for all $d$.

Normality for all $d\ge3$ remains open, and so does normality of $\alpha^2-2\alpha$ for any fixed $b$. The certificates exclude zero cells through degree 120 and on the listed infinite families. No general nonvanishing argument is proved. [Computations](../../scripts/phase16_dyadic_stoneham.py)

## 0. Status of the results

| Result | Status | Evidence |
| --- | --- | --- |
| Functional equation, base change $b\mapsto b^2$ (A.1) | Paper proof | 399 coefficient identities; $\kappa(b^2)-\kappa(b)$ for six radix pairs modulo $2^{100}$ |
| Transcendence of $C,\kappa_0$ over $\mathbb C(\lambda,e^{\lambda/2^m})$ (A.2) | Paper proof | Trace and pole arguments, no computation |
| Isometry of $\lambda\mapsto\kappa_0$, similarity for general $(A,B)$ (A.3) | Paper proof | Bijection on 1024 residues modulo $2^{12}$; random isometry and similarity checks |
| Metric statements in the parameter (A.4) | Paper proof | Borel–Cantelli, Baire category, covering |
| Integer recursion $Z_k$ and the normality criterion (A.5) | Lean + paper proof | `quadZ_closed_form`, `quadratic_upper_den_eq_quadZ` in Lean; $v_2(Z_k)=k+s+v_2(k-\kappa_0)$ (or both $\ge2k-1$) checked for $k\le8192$ and six radices; direct prefixes |
| Depth of $v_2(k-\kappa(b))$, $k\le10^6$ (A.6) | Finite computation | Two independent 128-bit evaluations of $\kappa(b)$ |
| No small algebraic relation for $\kappa(3),\kappa(5),\kappa(7)$ (A.6) | Finite computation, rigorous bound | Exact LLL with 512 bits |
| Truncation, integrality and digit automaton (B.1) | Paper proof | Automaton against the exact recurrence at 360 random cuts |
| $M_d\ne0$ on $[1,2)$ for $3\le d\le120$ (B.2) | Finite certificate | Branch and bound at minimal precision; Phase 14 tables for $d\le15$; exact recurrence at every leaf for $d\le24$, and at every maximal-loss witness, least-loss point and three random cuts for all $d\le120$ |
| Normality for degrees $3$–$120$ (B.2) | Certificate plus Phase 14 transfer | Same conditional Lean step as the Phase 14 degree-15 result |
| Cyclic descent and Lucas–Sylow reduction (B.3) | Paper proof | 84 exact congruences |
| Families $ep^r$ for seven pairs $(e,p)$ (B.3) | Finite certificate over $\mathbb F_p$ plus proof | Exhaustive vector orbits; exact spot values |
| Least-loss lower bound (B.4) | Paper proof | Orbit valuations |
| $F(d)=\sum\lfloor\log_2k\rfloor$; location of the least loss (B.4) | Finite computation, conjectured for all $d$ | DP for $d\le299$; orbit enumeration for $d\le64$; certificates for $d\le120$ |
| $v_2(M_d(1))=rd+2j$ when $\binom d{2j}$ is odd (B.5) | Paper proof | Exact values for $d\le120$ |

## Part A. The quadratic obstruction

### A.1 The functional equation and what it encodes

**Proposition A.1.** Put $c_1=1$ and $c_r=2^{r-1}/\bigl((1-2^{r-1})\,r!\bigr)$ for $r\ge2$. Then $C(\lambda)=\sum_{r\ge1}c_r\lambda^r$ and $\kappa_0(\lambda)=-\sum_{r\ge1}c_r\lambda^{r-1}$. Both series have 2-integral coefficients and converge on $2\mathbb Z_2$. They satisfy the two displayed identities of Theorem A.

*Proof.* Phase 14 shows $\delta_j-\lambda=\sum_{r\ge2}2^{j(r-1)}\lambda^r/r!$ and justifies summing over $j$ first. The geometric sum $\sum_{j\ge1}2^{j(r-1)}=2^{r-1}/(1-2^{r-1})$ in $\mathbb Q_2$ gives the series for $C$. Since $v_2(r!)\le r-1$, the coefficients are 2-integral, and each term has order at least $rv_2(\lambda)$. For the identity, $(2^r-2)c_r=-2^r/r!$ for every $r\ge2$, and the right side is the coefficient of $\lambda^r$ in $2\lambda+1-e^{2\lambda}$. The coefficient of $\lambda$ vanishes on both sides, because $c_1$ lies in the kernel of $C\mapsto C(2\lambda)-2C(\lambda)$. Division by $2\lambda$ gives the identity for $\kappa_0$. ∎

The equation determines $C$ up to the multiple $c_1\lambda$ of its kernel. Over $\mathbb C$ the same series is entire, and expanding $1/(1-2^{1-r})$ gives a dual expansion. The 2-adic sum runs over $2^{+j}$ and the archimedean one over $2^{-m}$.

```math
C(\lambda)=\lambda-\sum_{m\ge0}2^m\Bigl(e^{\lambda/2^m}-1-\frac{\lambda}{2^m}\Bigr).
```

**Proposition A.2 (base change).** $\alpha_{b,2}=\tfrac12\bigl(b^{-2}+\alpha_{b^2,2}\bigr)$ term by term, and $\lambda(b^2)=2\lambda(b)$. Then $P(\alpha_{b,2})$ with $P=X^2-2X$ is a rational quadratic in $\alpha_{b^2,2}$. After clearing it is $b^2Y^2+(2-4b^2)Y+\text{const}$, and its κ in radix $b^2$ is $\kappa_0(b)-1$. Shell $k$ in radix $b^2$ is shell $k+1$ in radix $b$.

So the functional equation is the self-similarity of the Stoneham number under squaring the radix. Normality in base $b$ and in base $b^2$ are equivalent, and the equation relates the problem only to an equivalent copy of itself. Iterating it from $\lambda$ to $2^n\lambda\to0$ reproduces the defining series $\kappa_0=-1-\lambda^{-1}\sum_j(\delta_j-\lambda)$. The script checks the identity $\kappa(b^2)-\kappa(b)=(b^{-2}-1-2\lambda)/(2\lambda)$ modulo $2^{100}$. It computes the two sides independently for $b=3,5,7,9,11,15$. It also checks the base change for $b=3,5,7,11$.

### A.2 Transcendence of the intercept

**Theorem A.3.** Let $m\ge0$ and $F_m=\mathbb C(\lambda,x)$ with $x=e^{\lambda/2^m}$, inside the field of meromorphic functions or of formal Laurent series. Then $C$ and $\kappa_0=-C/\lambda$ are transcendental over $F_m$, and hence over $\bigcup_mF_m\supset\mathbb Q(\lambda,e^{2\lambda})$.

*Proof.* Let $\sigma f(\lambda)=f(2\lambda)$, an injective endomorphism preserving $F_m$ (with $\sigma x=x^2$), which suffices for the minimal-polynomial trace step below. Put $g=2\lambda+1-x^{2^{m+1}}$, so $\sigma C=2C+g$. Suppose $C$ is algebraic over $F_m$ with monic minimal polynomial $P=X^n+p_{n-1}X^{n-1}+\cdots$. Applying $\sigma$ to $P(C)=0$ shows that $C$ is a root of $P^\sigma(2X+g)$, which has degree $n$ and leading coefficient $2^n$. By minimality $P^\sigma(2X+g)=2^nP(X)$. Comparing coefficients of $X^{n-1}$ gives $\sigma p_{n-1}-2p_{n-1}=-ng$. Therefore $h=-p_{n-1}/n\in F_m$ solves

```math
\sigma h-2h=2\lambda+1-x^{2^{m+1}} .
```

Since $e^{\lambda/2^m}$ is transcendental over $\mathbb C(\lambda)$, $F_m$ is a rational function field in $x$ over $K=\mathbb C(\lambda)$. Extend $\sigma$ to an algebraic closure $\bar K$ and decompose $h$ into partial fractions over $\bar K$. A nonzero pole ξ of $h$ produces poles of $\sigma h=h^\sigma(x^2)$ at the two distinct square roots of $\sigma\xi$. Distinct poles give disjoint pairs. The right side has no finite nonzero pole, so $\sigma h$ and $h$ have the same nonzero poles. Their number $N$ then satisfies $2N=N$, so $N=0$ and $h=\sum_nh_nx^n$ is a Laurent polynomial with $h_n\in\mathbb C(\lambda)$. Its $x^0$ coefficient satisfies $h_0(2\lambda)-2h_0(\lambda)=2\lambda+1$. The right side is a polynomial, so the nonzero poles $S$ of $h_0$ satisfy $S/2=S$. A finite set of nonzero complex numbers with this property is empty, so $h_0$ is a Laurent polynomial in λ. On such polynomials $\sigma-2$ multiplies the coefficient of $\lambda^n$ by $2^n-2$, which vanishes for $n=1$. So the coefficient of $\lambda$ on the left is 0, while on the right it is 2. This is a contradiction. The same argument applies to $\kappa_0$, since $\lambda\in F_m$. ∎

The obstruction is the linear term $2\lambda$, which lies in the kernel direction of $\sigma-2$. The particular solution $\lambda\log_2\lambda$ removes that term. Adjoining $\log\lambda$, with $\sigma\log\lambda=\log\lambda+\log2$, moves the obstruction to the exponential part. Growth along the positive real axis keeps $x$ transcendental over $\mathbb C(\lambda,\log\lambda)$, so the pole argument still applies. Odd coefficients vanish, and so do $h_{2^i}$ for $i\le m$. The $x^{2^{m+1}}$ coefficient then forces $h_{2^{m+1+i}}=2^{-1-i}\ne0$ for every $i\ge0$, but a Laurent polynomial has only finitely many nonzero coefficients. So $C$ remains transcendental over $\mathbb C(\lambda,\log\lambda,e^{\lambda/2^m})$. The archimedean expansion displays this infinite tower $e^{\lambda/2^m}$ explicitly.

*Remark (not used).* Write $\sigma\kappa_0-\kappa_0=\varphi$ with $\varphi=(x^2-1-2\lambda)/(2\lambda)$ and $x=e^\lambda$. A Hardouin–Singer criterion would make $\kappa_0$ differentially algebraic over $F_0$ only if some $L(\varphi)$, with $L$ a nonzero constant-coefficient polynomial in $\delta=\lambda\,d/d\lambda$, equals $\sigma f-f$ for some $f\in F_0$. The $x^2$ component of $L(\varphi)$ is $x^2P(\lambda\partial+2\lambda)(1/2\lambda)$. It is nonzero because $\lambda\partial+2\lambda$ has no rational eigenfunction. The same pole and Laurent argument then forces $f_{2^i}\ne0$ for all $i\ge1$. Hence no such certificate exists. We did not verify the constant-field hypotheses of their theorem here, so we draw no conclusion from this remark. It indicates that $C$ satisfies no algebraic differential equation of the kind a Schneider–Lang argument needs. [C. Hardouin and M. F. Singer, “Differential Galois theory of linear difference equations,” *Math. Ann.* 342 (2008), 333–377](https://doi.org/10.1007/s00208-008-0238-z)

### A.3 The parameter map is an isometry

**Theorem A.4.** Write $\kappa_0(\lambda)=\sum_{n\ge0}a_n\lambda^n$. Then $a_0=-1$, $a_1=1$, every $a_n$ is 2-integral, and $v_2(2a_2)=2$. For $x,y\in4\mathbb Z_2$,

```math
\kappa_0(x)-\kappa_0(y)=(x-y)\Bigl(1+\sum_{n\ge2}a_n\frac{x^n-y^n}{x-y}\Bigr),
```

and the bracket is $\equiv1\pmod 4$. Hence $\kappa_0$ is an isometry of $4\mathbb Z_2$ into $-1+4\mathbb Z_2$. It is onto, since it is bijective on $\mathbb Z/2^m$ for every $m$ and the domain is compact. On the sphere $v_2(\lambda)=s$ its derivative is $1+\tfrac49\lambda+\cdots=1+O(2^{s+2})$. With $\kappa_0=-\sum c_r\lambda^{r-1}$, the leading derivative term is $-c_2=+1$. Dropping the outer minus sign, as in $\sum_{r\ge2}(r-1)c_r\lambda^{r-2}$, would give $-1$. Either way the derivative is a unit.

The map $b\mapsto\lambda(b)=-\mathrm{Log}\,b$ sends $\mathbb Z_2^\times$ two-to-one onto $4\mathbb Z_2$, isometrically on each class $\pm1+4\mathbb Z_2$, and pushes Haar measure to Haar measure. So $b\mapsto\kappa_0(b)$ preserves the normalized measure and is isometric on each class modulo 4. The script checks the bijection on all 1024 residues $b\equiv1\pmod4$ modulo $2^{12}$, including $b=1$ with $\kappa_0(0)=-1$. It also checks the isometry on 200 random pairs of radices.

For general $A\ne0,B$ put $\beta=(2A+B)/(2A)$. Then $\kappa=\kappa_0-\beta/\lambda$, and $\kappa\in\mathbb Z_2$ exactly when $v_2(\beta)\ge s$. On a sphere $v_2(\lambda)=s$ the map $\lambda\mapsto\beta/\lambda$ multiplies distances by exactly $2^{2s-v_2(\beta)}$. When $v_2(\beta)\ne2s$ the ultrametric inequality therefore gives an exact similarity,

```math
|\kappa(x)-\kappa(y)|_2=2^{\max(0,\,2s-v_2(\beta))}|x-y|_2 .
```

On the critical sphere $v_2(\beta)=2s$, κ is a strictly convergent nonconstant power series in $\mu$, where $\lambda=2^s(1+2\mu)$. Constancy would make $\lambda^2\kappa_0'+\beta$ vanish on a disc, which Strassmann's theorem excludes since its constant term is $\beta\ne0$.

### A.4 Metric statements in the 2-adic parameter

**Corollary A.5.** Fix $A\ne0$ and $B$.

1. For Haar-almost every $\lambda\in4\mathbb Z_2$, equivalently almost every $b\in\mathbb Z_2^\times$, there is a constant $c$ such that $v_2(k-\kappa(\lambda))\le c\log_2k$ for all large $k$. One may take $c=1+\varepsilon$ for $\beta=0$ and off the critical sphere. Consequently $q_k\ge2^{k-O(\log k)}$.
2. Let $\beta=0$ and fix $c$. The set of λ with $v_2(k-\kappa_0(\lambda))\ge k-c$ for infinitely many $k$ is a dense $G_\delta$ in $4\mathbb Z_2$ of Hausdorff dimension zero. On it $q_k\le2^{c-a-s}$ infinitely often, and taking the union over $c\in\mathbb N$ characterizes all parameters with a bounded denominator subsequence. Every λ with $\kappa_0(\lambda)$ a positive integer has $q_k=1$ at that index. For general $(A,B)$, the same holds on each sphere $v_2(\lambda)=s$ with $v_2(\beta)\ge s$ and $v_2(\beta)\ne2s$ (the condition $v_2(\beta)\ge s$ ensures $\kappa\in\mathbb Z_2$, so positive integers $k$ lie in the image).

*Proof.* (1) For $\beta=0$, $\{\lambda:v_2(k-\kappa_0(\lambda))\ge m\}$ is the preimage of a ball of radius $2^{-m}$ under an isometric bijection. Its normalized measure is at most $2^{2-m}$. With $m_k=\lceil(1+\varepsilon)\log_2k\rceil$ the sum over $k$ converges, and Borel–Cantelli applies. Similarities with a fixed factor change only the constant. On the critical sphere Weierstrass preparation writes $\kappa-k$ as a unit times a distinguished polynomial of degree at most a fixed $N^\ast$. This gives measure $O(\rho^{1/N^\ast})$ for $|\kappa-k|_2\le\rho$ uniformly in $k$, and $c=N^\ast+\varepsilon$. (2) For each $k$, the set $\{v_2(k-\kappa_0)\ge k-c\}$ is the preimage of a ball of radius $2^{c-k}$, again a ball. The union over $k\ge K$ is open. It is dense: given a ball $B(\lambda_0,2^{-R})$, choose $k\equiv\kappa_0(\lambda_0)\pmod{2^R}$ with $k\ge K+R+c$. Then the preimage of $B(k,2^{c-k})$ lies in that ball, by the isometry. Baire's theorem applies to the intersection over $K$. For every σ>0, $\sum_k2^{-\sigma(k-c)}<\infty$ bounds the Hausdorff σ-measure by tails. ∎

**What this does and does not say.** Odd integers $b$ form a countable, Haar-null subset of $\mathbb Z_2^\times$. For non-integral 2-adic $b$ no real number $\alpha_{b,2}$ exists, so Corollary A.5 asserts normality of nothing. It shows that the arithmetic condition needed at integer $b$ holds for measure-theoretically typical parameters and fails for Baire-typical ones. That is the classical Liouville dichotomy, and it gives no conclusion for any particular integer. Its value is to show that bounded denominators require κ to be a 2-adic Liouville number of an extreme kind. Section A.5 makes this exact.

### A.5 A fixed radix: an elementary criterion and the obstruction

**Theorem A.6.** Let $P=X^2-2X$ and $Z_1=2-2b^2$, $Z_{k+1}=2+2b^{2^k}(Z_k-1)$. Then

```math
Z_k=1-2^kb^{2^k}+\sum_{j=1}^k2^{k-j}b^{2^k-2^j},\qquad
q_k=2^{[2k-1-v_2(Z_k)]_+},\qquad v_2(Z_k)=k+s+v_2(k-\kappa_0)\ \ (v_2(k-\kappa_0)<k-1+s).
```

*Proof.* With $T_k=\sum_{j\le k}\delta_j+\delta_k$, Phase 14 gives $q_k=2^{[k-v_2(2T_k)]_+}$ for $A=1,B=-2$. Multiplying $2^kT_k$ by $b^{2^k}$ gives the displayed sum $Z_k$, and the recursion follows by separating $j=k+1$. The expansion $T_k=k\lambda+C+E_k$ with $v_2(E_k)=k-1+2s$ gives the last formula. ∎

So $x=(\alpha^2-2\alpha)/D$ is normal in base $b$ if and only if $2k-v_2(Z_k)\to\infty$. Equivalently there is no constant $c$ with $|k-\kappa_0(b)|_2\le2^{c-k}$ for infinitely many positive integers $k$. In binary terms, normality fails exactly when, for infinitely many $m$, the 2-adic digits of $\kappa_0(b)$ vanish from about position $\log_2m$ to position $m$. Since $\kappa_0\equiv-1+\lambda\pmod{2^{2s}}$, only $k\equiv-1\pmod{2^s}$ can contribute. If $\kappa_0(b)$ is algebraic, Phase 14 already gives normality. The script checks that $v_2(Z_k)=k+s+v_2(k-\kappa_0)$ whenever $v_2(k-\kappa_0)<k-1+s$ (and otherwise both are $\ge2k-1$, yielding $q_k=1$) for every $k\le8192$ and the six radices. It also compares $Z_k$ with direct rational prefixes for $k\le8$.

**Where the standard methods stop.** Each step below is a precise mismatch, not a heuristic.

- *Mahler's method* (Mahler, Nishioka, Philippon's lifting, Adamczewski–Faverjon). In $z=e^\lambda$ the substitution $\lambda\mapsto2\lambda$ is $z\mapsto z^2$. The equation reads $C(\mathrm{Log}\,z^2)=2C(\mathrm{Log}\,z)+\mathrm{Log}\,z^2+1-z^2$, so its coefficient field contains $\mathrm{Log}\,z\notin\bar{\mathbb Q}(z)$, and $C\circ\mathrm{Log}$ is not meromorphic at $z=0$. More fundamentally, the evaluation is 2-adic at $z_0=\pm b^{-1}\in1+4\mathbb Z_2$. The iterates $z_0^{2^n}$ tend to the fixed point 1, where $z\mapsto z^2$ has multiplier 2 with $|2|_2=1/2$, rather than to the superattracting fixed point 0. An auxiliary function vanishing to order $T$ gains only $|2^n\lambda|_2^T=2^{-(n+s)T}$ after $n$ steps. The heights of $z_0^{2^n}=b^{\mp2^n}$ grow like $2^n\log b$, so Liouville's inequality allows values as small as $b^{-c2^n}$. The available smallness is exponential in $n$, while the Liouville bound is doubly exponential in $n$. This is the Phase 14 truncation obstruction in another form: precision $m$ costs height $2^m\log b$.
- *q-difference methods.* In λ the equation is a 2-adic $q$-difference equation with $q=2$ and $|q|_2<1$, which is the favourable direction. Transcendence theorems for such equations need coefficients in $\bar{\mathbb Q}(\lambda)$ and algebraic evaluation points. Here the inhomogeneity contains $e^{2\lambda}$. The point $\lambda_0=-\mathrm{Log}\,b$ is transcendental by Mahler's 2-adic Hermite–Lindemann theorem, while $e^{2\lambda_0}=b^{-2}$ is rational. Treating λ as a second unknown with $\sigma\lambda=2\lambda$ returns to the non-Mahler system above.
- *Schneider–Lang.* It needs an algebraic differential equation, of finite order, with algebraic values at many points. The pair $(\lambda,e^\lambda)$ satisfies this hypothesis and yields transcendence of $\mathrm{Log}\,b$. For $C$ no such equation is known, and the remark in A.2 indicates that none exists.
- *Two logarithms* (Bugeaud–Laurent). As recorded in Phase 14, this would require $\exp(-C)$ algebraic or $C$ a fixed linear form in logarithms. Theorem A.3 shows that $C$ is not even algebraic over $\mathbb C(\lambda,e^{\lambda/2^m})$.

Thus none of these methods reaches a fixed integer $b$, for the specific reasons listed.

### A.6 Numerical data

Two independent computations agree to 128 bits for $b\in\{3,5,7,9,11,15,25,49,81,121,225\}$. One uses the recurrence for $\delta_j$ and the other the λ-series with an independent 2-adic logarithm. For $b=3$ they reproduce the Phase 14 residues $\lambda\equiv5900$, $C\equiv2044$ and $\kappa\equiv15595\pmod{2^{16}}$.

| $b$ | $s$ | $\kappa_0(b)\bmod 2^{128}$ (hexadecimal) | $\max_{k\le10^6}v_2(k-\kappa_0)$ | at $k$ | $\max_{k\le10^6}\,(v_2(k-\kappa_0)-\log_2k)$ | at $k$ |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 3 | 2 | `7991aad778dc0774009895a536613ceb` | 21 | 81131 | 4.69 | 81131 |
| 5 | 2 | `079ec71a3eec59bae6e8c1d76fe609e3` | 21 | 395747 | 5.69 | 2531 |
| 7 | 3 | `af8a2250b5d0ec7d83ca504f157614a7` | 20 | 398503 | 4.63 | 5287 |
| 9 | 3 | `674ee960fe80d6e7d8262c3d53cbec97` | 22 | 781463 | 2.76 | 151 |
| 11 | 2 | `0d827f1eaa9108aa83e0369085b49933` | 20 | 301363 | 2.74 | 39219 |
| 15 | 4 | `ae4a24f652316d4bc9504a2b6a74528f` | 20 | 283279 | 3.63 | 21135 |

The candidates for both maxima are the least positive residues of $\kappa_0$ modulo $2^m$. The script confirms the reduction against a direct scan up to $10^5$. A random 2-adic κ would give about $2^{-x}\ln N$ indices with excess at least $x$. For $N=10^6$ that suggests a maximum excess near 3.8, and the observed range 2.7–5.7 is typical. There are no anomalously deep hits. The upper-shell exponent $k-1-s-v_2(k-\kappa_0)$ is at least $k-\log_2k-7-s$ for every $k\le10^6$.

*Exclusion of small algebraic values.* An exact LLL reduction is applied to the lattice of $(a_0,\dots,a_D)\in\mathbb Z^{D+1}$ with $\sum a_i\kappa^i\equiv0\pmod{2^{512}}$. The least Gram–Schmidt norm then bounds every nonzero lattice vector from below. For $b=3,5,7$ no integer polynomial of degree 1, 2 or 6 vanishing at $\kappa_0(b)$ has Euclidean coefficient norm below $2^{255}$, $2^{169}$ or $2^{72}$, respectively. This rules out an easy algebraic κ. It is consistent with transcendence and proves nothing about it.

## Part B. The leading mass in higher degree

### B.1 Integrality, truncation and the digit automaton

**Theorem B.1.** Let $d\ge1$.

1. $U_t=\{v:\sum_i2^{-v_i}\le t\}$ is a finitely generated upper set, so $M_d(t)=(-1)^dK_{U_t}(2)$ is an integer for every real $t$, with $K_U$ the Phase 13 orthant numerator.
2. The jump locations $\sum_i2^{-v_i}$ are sums of $d$ powers of 2. Their closure consists of dyadic numbers of binary weight at most $d$, and they accumulate only from the right. Hence $M_d(t)=M_d(\tau)$, where τ is $t$ truncated after its $d$-th binary digit 1. Every value of $M_d$ on $[1,2)$ occurs at such a dyadic τ, and $M_d$ is constant on $[2-2^{1-d},2)$.
3. For $1\le a\le d$ and $0\le n<a$ let state $(a,n)$ stand for $M_a(n+f)$ with $0\le f<1$. Reading the next digit $c$ of $f=(c+f')/2$ gives

   ```math
   M_a(n+f)=\sum_{m=0}^{n}\binom am2^{a-m}M_{a-m}\bigl(2(n-m)+c+f'\bigr).
   ```

   A target with $2(n-m)+c\ge a-m$ is absorbed with value $(-1)^{a-m}$. The weight of every transition between live states is divisible by $2^{a-n}\ge2$. Hence $M_d(t)\bmod2^L$ depends only on the first $L$ binary digits of $t$. Moreover every completion $f$ of a digit prefix satisfies $M_a(n+f)\equiv0\pmod{2^{a-n}}$.

*Proof.* (1) Dickson's lemma and the orthant expansion of the Phase 13 review give $K_U\in\mathbb Z[z]$, and the 2-adic series equals $K_U(2)/(1-2)^d$. (2) A sum of $d$ powers of two has at most $d$ binary ones. Let $\tau<x\le t$ with $x$ of weight at most $d$. Then $x$ agrees with τ through the $d$-th one of $t$ and has a further one, which is impossible. Limits of sums whose terms tend to zero approach from above. (3) Choosing the coordinates with deficit zero is the Phase 14 recurrence. The fractional part shifts identically in every branch, so only the integer part enters the state. Every live transition has $m\le n<a$. ∎

**Decision procedure.** Carry the vector of live coefficients and the absorbed value along a digit prefix. Let ν be the least order of a live coefficient times $2^{a-n}$. Every completion of the prefix changes the value at the prefix point by a multiple of $2^\nu$. If the value there has order below ν, the whole dyadic interval has that order, and the branch closes. A prefix with $d$ ones also closes by truncation. The procedure terminates at any precision. It returns a partition of $[1,2)$ into dyadic intervals with exact valuations, or exhibits a residue $0\bmod2^L$. In practice it needs a few hundred branch nodes, against the $7.3\times10^6$ multisets of the Phase 14 audit at degree 15.

The Phase 13 compactness argument takes the following concrete form. Valuations tending to infinity along a sequence of cells would converge, digit by digit, to a point of weight at most $d$ where $M_d=0$. So a degree without zero cells has a finite maximal loss, and branch and bound at that precision certifies it.

### B.2 Certificates through degree 120

**Theorem B.2.** For $3\le d\le120$ and every $t\in[1,2)$, $M_d(t)\ne0$. With $L_d=1+\max_tv_2(M_d(t))$, every residue is nonzero modulo $2^{L_d}$, and a witness attains order $L_d-1$. This precision is therefore least possible.

For $k\ge2L_d$ the Phase 14 transfer gives the exact denominator exponent $dk-v_2(M_d(t))$ of the shifted positive-index prefix of $\alpha^d$ at $n=t2^k$. Indeed every tuple of weight below $L_d$ has all deficits below $L_d$. It is therefore present, and its radix unit is $1\bmod2^{L_d}$, because $b^{2^j}\equiv1\pmod{2^{j+2}}$. A nonzero leading coefficient costs a fixed order. Lower powers have denominators dividing $2^{(d-1)k}$. The Phase 14 normality step then applies unchanged: insertions are sparse, tails are dominated, and the short-orbit estimate holds for odd radix. As for Phase 14's degree 15, the deduction uses this external certificate together with the conditional grid-to-normality step in Lean. [Retained-pole normality](../../NormalityChecker/StonehamPolynomialRetention.lean) · [Short-orbit estimate](../../NormalityChecker/SmoothOrbit.lean)

**Corollary B.3.** For every rational polynomial $P$ of degree $3\le\deg P\le120$, $P(\alpha_{b,2})$ is normal in base $b$, for every odd $b\ge3$.

For $d\le15$ the least precisions and witnesses coincide with Phase 14. For $d\le9$ the full valuation tables coincide with its multiset enumeration. For $d\le24$ the exact integer recurrence confirms the valuation at every leaf endpoint and just before the next. For $d\le12$ the procedure without the truncation shortcut gives the same tables. The full table follows. "Max at" is the least $t$ attaining the maximal loss.

<details>
<summary>Maximal and minimal losses for 3 ≤ d ≤ 120</summary>

| $d$ | Max loss | Max at | Min loss | $d$ | Max loss | Max at | Min loss | $d$ | Max loss | Max at | Min loss |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 6 | 9/8 | 3 | 43 | 243 | 1025/1024 | 197 | 83 | 544 | 4097/4096 | 457 |
| 4 | 8 | 1 | 7 | 44 | 247 | 271/256 | 204 | 84 | 546 | 1 | 465 |
| 5 | 15 | 65/64 | 9 | 45 | 261 | 16385/16384 | 209 | 85 | 565 | 8193/8192 | 471 |
| 6 | 24 | 149/128 | 12 | 46 | 266 | 619521/524288 | 215 | 86 | 568 | 4129/4096 | 478 |
| 7 | 24 | 169/128 | 14 | 47 | 268 | 257/256 | 220 | 87 | 580 | 2049/2048 | 484 |
| 8 | 33 | 1345/1024 | 20 | 48 | 274 | 287/256 | 229 | 88 | 577 | 1 | 493 |
| 9 | 35 | 513/512 | 23 | 49 | 289 | 65537/65536 | 234 | 89 | 595 | 16385/16384 | 499 |
| 10 | 36 | 19/16 | 27 | 50 | 292 | 537/512 | 240 | 90 | 597 | 1049/1024 | 506 |
| 11 | 45 | 561/512 | 30 | 51 | 300 | 1025/1024 | 245 | 91 | 608 | 4097/4096 | 512 |
| 12 | 46 | 79/64 | 35 | 52 | 301 | 1 | 252 | 92 | 614 | 1053/1024 | 520 |
| 13 | 55 | 257/256 | 38 | 53 | 321 | 65537/65536 | 257 | 93 | 623 | 8193/8192 | 526 |
| 14 | 59 | 375/256 | 42 | 54 | 321 | 2081/2048 | 263 | 94 | 627 | 517/512 | 533 |
| 15 | 64 | 133/128 | 45 | 55 | 329 | 513/512 | 268 | 95 | 637 | 4177/4096 | 539 |
| 16 | 67 | 6785/4096 | 53 | 56 | 331 | 1121/1024 | 276 | 96 | 650 | 2127/2048 | 550 |
| 17 | 77 | 4097/4096 | 57 | 57 | 345 | 32769/32768 | 281 | 97 | 659 | 65537/65536 | 556 |
| 18 | 83 | 521/512 | 62 | 58 | 347 | 537/512 | 287 | 98 | 662 | 1049/1024 | 563 |
| 19 | 88 | 257/256 | 66 | 59 | 356 | 2115/2048 | 292 | 99 | 672 | 4097/4096 | 569 |
| 20 | 89 | 1 | 72 | 60 | 360 | 1081/1024 | 299 | 100 | 674 | 1 | 577 |
| 21 | 100 | 1025/1024 | 76 | 61 | 370 | 8193/8192 | 304 | 101 | 689 | 8193/8192 | 583 |
| 22 | 111 | 1149/1024 | 81 | 62 | 375 | 2081/2048 | 310 | 102 | 694 | 1033/1024 | 590 |
| 23 | 109 | 129/128 | 85 | 63 | 382 | 519/512 | 315 | 103 | 702 | 2049/2048 | 596 |
| 24 | 112 | 1 | 92 | 64 | 395 | 1095/1024 | 327 | 104 | 705 | 1 | 605 |
| 25 | 124 | 2049/2048 | 96 | 65 | 403 | 131073/131072 | 333 | 105 | 720 | 16385/16384 | 611 |
| 26 | 129 | 561/512 | 101 | 66 | 407 | 4105/4096 | 340 | 106 | 730 | 1049/1024 | 618 |
| 27 | 134 | 257/256 | 105 | 67 | 417 | 4097/4096 | 346 | 107 | 737 | 4097/4096 | 624 |
| 28 | 140 | 285/256 | 111 | 68 | 422 | 1037/1024 | 354 | 108 | 739 | 527/512 | 632 |
| 29 | 150 | 5041/4096 | 115 | 69 | 434 | 8193/8192 | 360 | 109 | 751 | 8193/8192 | 638 |
| 30 | 152 | 529/512 | 120 | 70 | 438 | 1033/1024 | 367 | 110 | 755 | 517/512 | 645 |
| 31 | 164 | 2097/2048 | 124 | 71 | 447 | 2049/2048 | 373 | 111 | 765 | 1025/1024 | 651 |
| 32 | 163 | 633/512 | 134 | 72 | 452 | 2141/2048 | 382 | 112 | 769 | 543/512 | 661 |
| 33 | 180 | 262145/262144 | 139 | 73 | 465 | 16385/16384 | 388 | 113 | 786 | 32769/32768 | 667 |
| 34 | 178 | 67/64 | 145 | 74 | 472 | 8593/8192 | 395 | 114 | 792 | 8385/8192 | 674 |
| 35 | 190 | 1025/1024 | 150 | 75 | 484 | 4097/4096 | 401 | 115 | 799 | 4097/4096 | 680 |
| 36 | 190 | 1 | 157 | 76 | 485 | 527/512 | 409 | 116 | 801 | 1 | 688 |
| 37 | 209 | 262145/262144 | 162 | 77 | 496 | 8193/8192 | 415 | 117 | 817 | 8193/8192 | 694 |
| 38 | 211 | 4369/4096 | 168 | 78 | 500 | 517/512 | 422 | 118 | 823 | 8433/8192 | 701 |
| 39 | 214 | 513/512 | 173 | 79 | 516 | 133633/131072 | 428 | 119 | 831 | 8483/8192 | 707 |
| 40 | 217 | 1 | 181 | 80 | 514 | 543/512 | 438 | 120 | 835 | 2157/2048 | 716 |
| 41 | 233 | 32769/32768 | 186 | 81 | 529 | 32769/32768 | 444 | | | | |
| 42 | 235 | 537/512 | 192 | 82 | 541 | 33537/32768 | 451 | | | | |

</details>

Three regularities persist through degree 120. For every $d\ge17$ the maximal loss first occurs in $[1,5/4)$. Typically it falls at $t=1+2^{-a}$ for moderate $a$. For $d\in\{4,20,24,36,40,52,84,88,100,104,116\}$, all divisible by 4, it falls at $t=1$ itself. It exceeds the minimal Kraft weight $rd+2j$ ($d=2^r+j$, Proposition B.8) by at most 14, with equality at $d=37$ and $d=53$. The least loss obeys the formula of B.4. The partitions at precision $L_d$ have at most 373 leaves.

### B.3 Cyclic descent modulo odd primes and infinite families

**Theorem B.4 (cyclic descent).** Let $p$ be an odd prime, $r\ge1$, $e\ge1$ and $d=p^re$. For every real $t\in(0,p^r)$, $M_d(t)\equiv M_e(t/p^r)\pmod p$. For $t\in[1,2)$ and $y=2^jt/p^r\in[1,2)$, this reads $M_d(t)\equiv2^{ej}M_e(y)\pmod p$.

*Proof.* Split the $d$ coordinates into $e$ blocks of length $p^r$ and let $H\cong C_{p^r}$ rotate all blocks at once. On each finite weight slice of $U_t$, orbits of size greater than one contribute zero modulo $p$. The fixed tuples are constant on blocks, and they lie in $U_t$ exactly when the block values lie in $U^{(e)}_{t/p^r}$. Hence

```math
F_{U_t}(z)\equiv F_{U^{(e)}_{t/p^r}}(z^{p^r}),\qquad
K_{U_t}(z)=(1-z)^dF_{U_t}(z)\equiv(1-z^{p^r})^eF_{U^{(e)}}(z^{p^r})=K_{U^{(e)}}(z^{p^r})\pmod p .
```

Evaluate at $z=2$ and use $2^{p^r}\equiv2\pmod p$. The signs agree because $d\equiv e\pmod2$. Since $p\ge3$ and $t\in[1,2)$, we have $t/p^r\in(0,2/3)\subset(0,1)$, so each doubling step $x\mapsto 2x$ starts strictly below $1$ (where no coordinate can have deficit zero, giving $M_e(x)=2^eM_e(2x)$) until the final normalized cutoff $y=2^jt/p^r$ enters $[1,2)$ (including $y=1$ if $t/p^r=2^{-j}$, and values arbitrarily close to $2$). ∎

The case $e=1$ is the Phase 13 theorem, since $M_1=-1$ on $[1,2)$. More generally, Sylow subgroups of $S_d$ give $M_d(t)\equiv M_{\mathbf s}(t)\pmod p$, where the block sizes $\mathbf s$ are the powers $p^k$ in the base-$p$ digits of $d$. Here $M_{\mathbf s}(t)=\sum2^{|w|}$ over $w$ with $\sum_\beta s_\beta2^{-w_\beta}\le t$, and the proof uses the multigraded orthant numerator and $2^{p^k}\equiv2$. Only the single-digit case is uniform in the digit position, which is what Theorem B.4 exploits.

**Corollary B.5.** Call $(e,p)$ good if $M_e(y)\not\equiv0\pmod p$ for every $y\in[1,2)$. Then every degree $ep^r$, $r\ge0$, has no zero cell, by compactness has a finite maximal loss, and has normal values at α for all rational polynomials. The following pairs are good:

| $e$ | $p$ | $\operatorname{ord}_p2$ | New degrees beyond 120 |
| ---: | ---: | ---: | --- |
| 3 | 31 | 5 | $3\cdot31^r$, $r\ge2$ (2883, 89373, …) |
| 3 | 127 | 7 | $3\cdot127^r$, $r\ge1$ |
| 3 | 257 | 16 | $3\cdot257^r$, $r\ge1$ |
| 3 | 337 | 21 | $3\cdot337^r$, $r\ge1$ |
| 3 | 1801 | 25 | $3\cdot1801^r$, $r\ge1$ |
| 3 | 8191 | 13 | $3\cdot8191^r$, $r\ge1$ |
| 4 | 8191 | 13 | $4\cdot8191^r$, $r\ge1$ (even degrees) |

*Certificate.* By B.1, the set of values of $M_e$ on $[1,2)$ modulo $p$ equals $\{\rho\cdot V\}$. Here ρ runs over the vectors reachable from the start state under the two digit matrices over $\mathbb F_p$. This finite orbit is exhausted, and 0 does not occur. Exact integer values at cuts of binary weight at most $e$ give an independent spot check.

**Why descent cannot reach every degree.** For $e=2$ one has exactly $M_2(1)=4$ and $M_2(t)=4-2^{a+1}$ on $[1+2^{-a},1+2^{1-a})$, which includes the zero cell $[3/2,2)$. This vanishes modulo $p$ whenever $\operatorname{ord}_p2\mid a-1$, so no odd prime is good for $e=2$. Phase 13 fails in degree four already at the zero-mass corner of a symmetric upper set. For the actual cut, the reduced mass of degree $2p^r$ vanishes modulo $p$ on infinitely many cells. For $e\ge3$, $M_e$ takes infinitely many values given by exponential polynomials in the positions of the binary ones. For example, $M_3(1+2^{-a}+2^{-a-1})=32-3\cdot2^{a+2}$ for $a\ge2$. Such values vanish modulo most primes. Degree 15 shows the failure concretely. Descent at $p=5$ meets $M_3(3/2)=40\equiv0\pmod5$, and $3$ is not good for $e=5$. So Phase 14 needed its 2-adic certificate there. Good primes are rare and have small $\operatorname{ord}_p2$. Among primes below 60 the only good ones for $e\le5$ are $p\in\{3,31\}$ for $e=3$ and $p=5$ for $e=5$. A search over the 23 primes below $10^5$ with $\operatorname{ord}_p2\le25$, for $3\le e\le7$, found exactly the table above, apart from the trivial pairs $p=e$ with $e=3,5,7$. For $e=6$ four primes and for $e=7$ ten primes exceeded the orbit cap of $4\cdot10^5$ vectors and remain undecided. The option `--descent-search` repeats this search. Powers of two $d=2^r$ admit no descent at all, and among them only $4,\dots,64$ are certified, through Theorem B.2.

### B.4 Where the least loss sits

Group an orbit by the multiplicities $c_i$ of each deficit $i$. Its contribution to $M_d$ is $\binom{d}{c_0,c_1,\dots}2^{\sum ic_i}$, which has order $v_2(d!)+\Phi(c)$ with

```math
\Phi(c)=\sum_i\bigl(ic_i-v_2(c_i!)\bigr)=\sum_i\bigl((i-1)c_i+s_2(c_i)\bigr),
```

where $s_2$ is the binary digit sum. Let $F(d)$ be the minimum of Φ over multisets with $\sum_ic_i2^{-i}<2$.

**Proposition B.6.** For every $t\in[1,2)$, $v_2(M_d(t))\ge v_2(d!)+F(d)$. If exactly one orbit with $\Phi=F(d)$ lies in $U_t$, equality holds.

**Computation and conjecture B.7.** An exact dynamic programme over the number of zero deficits verifies $F(d)=\sum_{k=1}^d\lfloor\log_2k\rfloor$ for $d\le299$. More generally it verifies the closed form

```math
\min_{\sum_i c_i=d,\ \sum_i c_i2^{-i}<2^a}\ \sum_i\bigl(ic_i+s_2(c_i)\bigr)=a+\sum_{k=2^a}^{d}\bigl(\lfloor\log_2k\rfloor-a+2\bigr)\quad(d\ge2^a),
```

with value $s_2(d)$ for $d<2^a$. This is checked for $d<200$ and $a\le7$, and $a=1$ is the identity for $F(d)$. Write $2^r-1\le d\le2^{r+1}-2$ and $j=d-2^r+1$. For $d\le64$ an exhaustive enumeration finds exactly two minimizing orbits when $j\ge1$:

```math
\{(r-1)^{2^r-j-1},\,r^{2j}\}\ \text{at}\ 2-2^{1-r},\qquad \{(r-1)^{2^r-j},\,r^{2j-1}\}\ \text{at}\ 2-2^{-r}.
```

For $j=0$ the single minimizer is $(r-1)^d$ at $2-2^{1-r}$. Proposition B.6 then gives the least loss $v_2(d!)+\sum_{k\le d}\lfloor\log_2k\rfloor$ exactly on $[2-2^{1-r},2-2^{-r})$, or on $[2-2^{1-r},2)$ when $j=0$. Everywhere else the loss is strictly larger. The branch-and-bound certificates confirm this least loss for every $d\le120$. A proof of $F(d)=\sum\lfloor\log_2k\rfloor$ for all $d$ is open, and the obvious relaxations fail. Charging each run of equal deficits the slack of its own sorted positions fails already for one deficit-1 coordinate followed by four deficit-2 coordinates, even though the total inequality holds. Replacing the Kraft bound by the per-level caps $c_i\le2^{i+1}-1$ gives a strictly smaller minimum from $d=3$. Rounding the intermediate Kraft bounds up to powers of two does so from $d=7$.

The least loss controls only the *upper* bound on denominators. Nonvanishing concerns the maximal loss. Ties between minimal orbits are common there. For $3\le d\le20$, 20% to 63% of the leaves of the partition computed at precision $8d+40$ have valuation above the least orbit order of their cut. Every such leaf has an even number of minimal orbits. Every leaf at the least order has an odd number. A dominant-orbit argument therefore cannot prove nonvanishing in general.

### B.5 Special cutoffs and the interval $[3/2,2)$

**Proposition B.8 (the Kraft point).** Write $d=2^r+j$ with $0\le j<2^r$. The minimum of $\sum v_i$ subject to $\sum2^{-v_i}\le1$ is $rd+2j$. It is attained only by $2^r-j$ deficits $r$ and $2j$ deficits $r+1$, an orbit of size $\binom d{2j}$. Hence $v_2(M_d(1))\ge rd+2j$, with equality when $\binom d{2j}$ is odd. In particular $v_2(M_{2^r}(1))=r2^r$.

*Proof.* Replacing deficits $u+2\le w$ by $u+1,w-1$ keeps the weight and strictly lowers the Kraft sum. For a fixed degree $d$, the unique balanced configuration of total weight $W=qd+m$ ($0\le m<d$) has $d-m$ deficits $q$ and $m$ deficits $q+1$, with Kraft sum $(d-m)2^{-q}+m2^{-q-1}=(2d-m)2^{-q-1}$, which strictly decreases as $W$ increases. At $W=rd+2j$ this balanced Kraft sum equals $(2d-2j)2^{-r-1}=1$; therefore every configuration of weight $<rd+2j$ has Kraft sum strictly greater than $1$, and the balanced configuration of weight $rd+2j$ is the unique minimizer in $U_1$. Every other orbit in the cut has larger weight. ∎

The exact values are $M_d(1)=4,32,2304,376832,\dots$, $M_d(2^-)=0,-8,-256,-21504,\dots$ and $M_d(3/2)=0,40,1152,196096,\dots$ for $d=2,3,4,5$. Their odd parts show no closed form through $d=30$. For instance $M_6(1)=2^{16}\cdot5\cdot11\cdot41$. The script verifies Proposition B.8 for $d\le120$, both its exact cases and the strict inequality in the others. It also verifies the constancy of $M_d$ on $[2-2^{1-d},2)$.

*The interval $[3/2,2)$.* On $[1,2)$, $M_d(t)=2^dM_d(2t)+d2^{d-1}M_{d-1}(2t-2)$. For $d=3$ and $t\ge3/2$ the first term is $8\cdot(-1)$, so $M_3=-8+12M_2(2t-2)$. This equals $40-24\cdot2^a$ on the cells of $M_2$ and $-8$ on $[7/4,2)$. For $d\ge4$, however, $M_d$ is not constant on $[3,4)$. Tuples $(0,0,0,v)$ enter at $3+2^{-v}$, so infinitely many cells remain, and the recursion does not close. The data confirm that $[3/2,2)$ has no special status beyond containing the least-loss interval of B.4. For every $d\le64$ other than $2^r-1$, the subinterval $[2-2^{-r},2)$ carries two tied minimal orbits. We found no clean theorem for $[3/2,2)$ in general degree.

### B.6 Partial nonvanishing and zero cells

Nonvanishing on a subinterval of $[1,2)$ does not suffice. The remaining cells carry a fixed positive proportion of every shell's positions. On such cells the polynomial's denominators must be controlled separately. On an actual zero cell of $M_d$ the cut is one fixed upper set, and the Phase 14 secondary analysis applies. For a **pure power** $\alpha^d$ it gives exponent $(d-1)k-\nu_2(d)-u$ when $a\ne0$, which still tends to infinity. When $a=0$ the loss beyond $(d-1)k$ is unbounded along a sparse set of shells. That analysis then gives no lower bound tending to infinity, and the question becomes a 2-adic approximation problem of the same kind as the quadratic one. For a general polynomial, the term $c_{d-1}\alpha^{d-1}$ has its own pole of order $(d-1)k-O(1)$ and can cancel this secondary pole. Nonvanishing of $M_d$ everywhere on $[1,2)$ is the clean condition uniform in $P$. Since no zero cells occur for $d\le120$ or in the families of B.3, this alternative is not needed there.

## Open boundaries

1. **Fixed radix quadratic.** Decide whether $2k-v_2(Z_k)\to\infty$ for the integers of Theorem A.6, for any single $b$. Equivalently, decide whether $|k-\kappa_0(b)|_2\le2^{c-k}$ fails eventually for each $c$. Algebraicity of $\kappa_0(b)$ would suffice and is open. A.5 explains why the functional equation adds nothing for fixed $b$.
2. **All degrees.** Prove $M_d\ne0$ on $[1,2)$ for every $d\ge3$. Beyond 120 only the odd prime powers and the families of B.3 are known. In particular nothing is known for $d=2^r$ with $r\ge7$, or for $d=2p^r>120$. Cyclic descent provably cannot reach the latter.
3. **Least loss.** Prove $F(d)=\sum_{k\le d}\lfloor\log_2k\rfloor$ and the two-orbit structure for all $d$, or the closed form for every Kraft bound $2^a$.
4. **Maximal loss.** Bound $\max_tv_2(M_d(t))-(rd+2j)$ uniformly. It is at most 14 for $d\le120$. Any bound of this type would prove nonvanishing for all degrees.

## Reproduction

From the repository root:

```sh
python -B scripts/phase16_dyadic_stoneham.py                    # Part A, certificates d <= 64
python -B scripts/phase16_dyadic_stoneham.py --max-degree 120   # full table (about eight minutes)
python -B scripts/phase16_dyadic_stoneham.py --quick            # shorter searches, d <= 40
```

The script uses only the Python standard library, and all arithmetic is exact integer or rational. The only floating-point steps are the archimedean check of A.1 and the printed excess logarithms. Its Phase 14 cross-check imports `scripts/phase14_dyadic_power_cells.py`.
