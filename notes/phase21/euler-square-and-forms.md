# Euler's square and binary quadratic forms in every radix

Phase 21, Tracks A3 and A4. Notation follows [radix-lambert.md](radix-lambert.md): $D_N(z;b)$ is the extreme discrepancy of $\{b^nz\}$, $0\le n<N$, $LL=\log\log N$, $\ell_N=\log_b\log N$, and Theorem 1 there is the **sub-threshold width law**. All deficits below also equal $\sup_x|D_N(x+z;b)-D_N(x;b)|$ by sharp translation.

**Theorem A3 (paper proof, granting the cited eigenform input).** Let $E_b=\prod_{k\ge1}(1-b^{-k})$, $E_b^2=\sum_{n\ge0}a_2(n)b^{-n}$ and $S_\eta(N)=\#\{1\le n\le N:a_2(n)\ne0\}$. Then

```math
S_\eta(N)\sim C_\eta\frac N{(\log N)^{3/4}},\qquad
C_\eta=\frac{12}{\Gamma(1/4)}\Bigl(\frac{\pi^2\log(2+\sqrt3)}{54}\prod_{\substack{p\ge5\\ p\not\equiv1\ (12)}}\Bigl(1-\frac1{p^2}\Bigr)^{-2}\Bigr)^{1/4}=2.418529\ldots,
```

and

```math
1-D_N(E_b^2;b)\sim
\begin{cases}
\dfrac{3\,C_\eta}{4\log b}\,\dfrac{\log\log N}{(\log N)^{3/4}}, & b=2^k,\\[2ex]
\dfrac{C_\eta\,(3+\log2)}{4\log b}\,\dfrac{\log\log N}{(\log N)^{3/4}}, & b\ \text{not a power of }2.
\end{cases}
```

The split-prime density is $\delta=\frac14$ (primes $p\equiv1\pmod{12}$), so $\delta\log2=0.173<\kappa=\frac34$. $E_b^2$ lies strictly below the threshold $\delta^*=1/(1+\log2)$, and both constants are unconditional given the inputs. The coefficients are signed, and half of the nonzero ones are negative. Two-sided isolation makes the signs harmless (§1.4).

**Theorem A4 (paper proofs).** Let $Q$ be a positive definite integral binary quadratic form, let $S_Q(N)=\#\{1\le n\le N:r_Q(n)>0\}\sim C_QN/\sqrt{\log N}$ (Bernays), and put $\Psi_N=C_Q\log\log N/(2\log b\sqrt{\log N})$.

1. **Complete lower bound, every $Q$ and every $b$.** $\liminf(1-D_N(\Theta_Q(1/b);b))/\Psi_N\ge1$. This holds for primitive and imprimitive $Q$ of any discriminant (§2.2).
2. **Class number one**, fundamental $\Delta\in\{-3,-4,-7,-8,-11,-19,-43,-67,-163\}$. Here $r_Q=w(1*\chi_\Delta)$, $C_Q=C_{\chi_\Delta}$, and $1-D_N\sim\Psi_N$ for $b=2^k$, $1-D_N\sim(1+\log2)\Psi_N$ otherwise.
3. **One class per genus** ($h_0=h/g=1$, fundamental $\Delta$; for example $\Delta=-20,-24$). Here $r_Q=w(1*\chi_\Delta)\mathbf 1_{\rm genus}$, $C_Q=C_{\chi_\Delta}/g$, with the same two constants as in part 2.
4. **Several classes per genus** ($h_0>1$, fundamental $\Delta$). For almost all $n$ represented by $Q$, $r_Q(n)=(1+o(1))\,w(1*\chi_\Delta)(n)/h_0$, so $r_Q(n)$ concentrates at $2^{\omega_{\rm split}(n)}\cdot w/h_0$ up to a tight odd factor. In every radix,

```math
1\le\liminf\frac{1-D_N}{\Psi_N}\le\limsup\frac{1-D_N}{\Psi_N}\le
\begin{cases}1+(1-h_0^{-1})\log2, & b=2^k,\\ 1+\log2, & \text{otherwise.}\end{cases}
```

5. **Class group $\mathbb Z/3$** (fundamental $\Delta$; for example $\Delta=-23$). The upper value $1+\log2$ is the limit in every radix that is not a power of $2$. In radix $2^k$ the limit is

```math
1+\tfrac23(1-\pi_J)\log2,\qquad 1-\pi_J=\prod_{p\ \text{nonprincipal split}}\Bigl(1-\frac{(1-1/p)\,p^{-2}}{1-p^{-3}}\Bigr).
```

  For $\Delta=-23$, $1-\pi_J=0.783637\ldots$, $\pi_J=0.216363\ldots$ (verified to $p\le5\cdot10^6$; the script's truncation at $p\le65{,}640$ gives $0.783638$ / $0.216362$), and the factor is $1.362117\ldots$, strictly between the class-number-one value $1$ and the value $1+\log2=1.693$ for other radices.

Thus the dichotomy between radix $2^k$ and other radices is proved unconditionally for fundamental $\Delta$ with $h_0=1$ or $\mathrm{Cl}(\Delta)\cong\mathbb Z/3$, and conditionally (under $(\mathrm V_q)$) for all fundamental $\Delta$ (since $1+(1-h_0^{-1})\log 2<1+\log 2$), with the radix-$2^k$ constant depending on the $2$-structure of the class group. Outside radix $2^k$ it is $1+\log2$ whenever it is known; for non-fundamental and imprimitive forms, only the order and the lower value $1$ are proved here.

**Scope and evidence.** Paper proofs from Theorem 1 of [radix-lambert.md](radix-lambert.md), Phase 20's finite lemmas (circle separation kernel-verified as `CoefficientTransfer.one_sub_discrepancy_ge_of_bulk_and_far`), and published inputs:

- Selberg–Delange (Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, II.5);
- Halberstam–Richert and Shiu upper bounds;
- Brun's sieve;
- Bernays (1912) and the genus theory of binary forms;
- the equidistribution of prime ideals in ideal classes (Hecke; equivalently Chebotarev in the Hilbert class field, unconditional for a fixed field);
- the Sathe–Selberg local law (only in part 5);
- for A3, the cited fact that $\eta(12\tau)^2$ is a CM Hecke eigenform ([Phase 20, Theorem 6](../phase20/euler-product.md#5-the-square-of-eulers-product)).

[`scripts/phase21_radix.py`](../../scripts/phase21_radix.py) verifies the factorization criterion for every $n\le10^6$, the Euler product and second-order term of $C_\eta$ against exact counts, every representation-number identity used below for $n\le65{,}640$, and certified discrepancies. Ratios to the asymptotic laws are finite measurements.

## 1. Euler's square (Track A3)

### 1.1 Coefficients and support

By Phase 20 Theorem 6(a), $a_2(n)=c(12n+1)$ with $c$ multiplicative:

- $c(p^e)=(e+1)\epsilon_p^e$ with $\epsilon_p=\pm1$ for $p\equiv1\pmod{12}$;
- $c(p^{2e+1})=0$ and $c(p^{2e})=(-\chi_{-4}(p))^e$ for the other $p\ge5$;
- $c(2^e)=c(3^e)=0$ for $e\ge1$.

So $a_2(n)\ne0$ exactly when $12n+1\in\mathcal S$, where $\mathcal S$ is the set of integers coprime to $6$ in which every prime $p\not\equiv1\pmod{12}$ has even exponent; then $|a_2(n)|=\prod_{p\equiv1\,(12)}(v_p(12n+1)+1)$. Every element of $\mathcal S$ is $\equiv1\pmod{12}$, since $p^2\equiv1\pmod{24}$ for $p\nmid6$. Hence

```math
S_\eta(N)=S_{\mathcal S}(12N+1)-1,\qquad S_{\mathcal S}(x)=\#\{m\le x:m\in\mathcal S\}.
```

The script computes $a_2(n)$ for $n\le10^6$ by convolving the pentagonal series, factors every $12n+1$ by a progression sieve, and checks the criterion **for every $n\le10^6$**, extending Phase 20's check to $2^{17}$. There are $307{,}819$ nonzero coefficients, $153{,}878$ of them negative.

### 1.2 The constant $C_\eta$

Let $F(s)=\sum_{m\in\mathcal S}m^{-s}=\prod_{p\equiv1\,(12)}(1-p^{-s})^{-1}\prod_{p\ge5,\,p\not\equiv1\,(12)}(1-p^{-2s})^{-1}$. The four characters modulo $12$ are $\chi_0^{(12)}$, $\chi_{-4}^{(12)}$, $\chi_{-3}^{(12)}$ and $\chi_{12}$. At a prime $p\not\equiv1\pmod{12}$, $p\ge5$, two of them take the value $+1$ and two the value $-1$, so their Euler factors multiply to $(1-p^{-2s})^{-2}$. Hence

```math
F(s)^4=L(s,\chi_0^{(12)})L(s,\chi_{-4}^{(12)})L(s,\chi_{-3}^{(12)})L(s,\chi_{12})\prod_{\substack{p\ge5\\ p\not\equiv1\,(12)}}(1-p^{-2s})^{-2},
```

with $L(s,\chi_0^{(12)})=\zeta(s)(1-2^{-s})(1-3^{-s})$. The imprimitive characters $\chi_{-4}^{(12)}$ and $\chi_{-3}^{(12)}$ are induced from the primitive characters $\chi_{-4}$ (mod $4$) and $\chi_{-3}$ (mod $3$), contributing the Euler factors $(1+3^{-s})$ and $(1+2^{-s})$. Using $L(1,\chi_{-4})=\pi/4$, $L(1,\chi_{-3})=\pi/(3\sqrt3)$ and $L(1,\chi_{12})=\log(2+\sqrt3)/\sqrt3$ (class number one, fundamental unit $2+\sqrt3$),

```math
\lim_{s\to1^+}(s-1)F(s)^4=\frac12\cdot\frac23\cdot\frac\pi4\cdot\frac43\cdot\frac{\pi}{3\sqrt3}\cdot\frac32\cdot\frac{\log(2+\sqrt3)}{\sqrt3}\prod(1-p^{-2})^{-2}=\frac{\pi^2\log(2+\sqrt3)}{54}\prod(1-p^{-2})^{-2}.
```

The Selberg–Delange theorem with $z=\frac14$ (Tenenbaum, Theorem II.5.3) gives $S_{\mathcal S}(x)=x(\log x)^{-3/4}\bigl(\lambda_0+\lambda_1/\log x+O(\log^{-2}x)\bigr)$, where

```math
\lambda_0=\frac{G(1)}{\Gamma(1/4)},\qquad\frac{\lambda_1}{\lambda_0}=-\frac34\,\frac{d}{ds}\log\frac{(s-1)^{1/4}F(s)}{s}\Big|_{s=1},\qquad G(s)=(s-1)^{1/4}F(s).
```

Since $S_\eta(N)=S_{\mathcal S}(12N+1)-1$ and $\log(12N)\sim\log N$, $C_\eta=12\lambda_0$.

The second-order coefficient needs $L'/L(1,\chi)$. For the odd characters the functional equation and Lerch's formula give $L'/L(1,\chi)=\gamma+\log2\pi-\sum_a\chi(a)\log\Gamma(a/q)/L(0,\chi)$. This yields $0.245610$ for $\chi_{-4}$ and $0.368282$ for $\chi_{-3}$; the script checks both against direct summation. For $\chi_{12}$ the value $0.476750$ comes from rapidly convergent direct summation. The same formula for Landau–Ramanujan reproduces Shanks's second-order constant $0.581949$ to $2\cdot10^{-4}$, which the script asserts as a check of the method. For $\mathcal S$ it gives $\lambda_1/\lambda_0=0.43361$.

| $N$ | $S_\eta(N)$ | $S_\eta(\log N)^{3/4}/N$ | exact / one-term | exact / two-term | residual $\cdot\log^2x$ |
|---|---|---|---|---|---|
| $10^4$ | 4,019 | 2.1248 | 1.0512 | 1.01360 | 1.861 |
| $10^5$ | 34,787 | 2.1742 | 1.0409 | 1.00966 | 1.893 |
| $5\cdot10^5$ | 159,292 | 2.1965 | 1.0344 | 1.00640 | 1.558 |
| $10^6$ | 307,819 | 2.2058 | 1.0325 | 1.00576 | 1.530 |

Here $x=12N+1$. The relative residual of the two-term law, multiplied by $\log^2x$, stays in $[1.5,1.9]$, as a third-order term predicts. Phase 20's measured values $2.107$–$2.206$ of $S(\log N)^{3/4}/N$ lie below $C_\eta=2.4185$ mainly because $(\log N/\log12N)^{3/4}=0.88$ at $N=2^{20}$. The constant itself rests on the Euler product above.

### 1.3 Proof of the discrepancy constants

Apply Theorem 1 to $a=a_2$ with $\kappa=\frac34$ and $B=0$.

- **(W1).** By Phase 20 Theorem 6(b), $\sum_{n\le X}|a_2(n)|\ll X/\sqrt{\log X}$. Pointwise, $|a_2(n)|\le\tau(12n+1)=n^{o(1)}$.
- **(W2) Pairs.** If $a_2(n)a_2(n+h)\ne0$, then $12n+1$ and $12n+12h+1$ lie in $\mathcal S$. Discard the $n$ for which $q^2$ divides either number for some $q>z_0=(\log N)^2$ with $q\not\equiv1\pmod{12}$; there are $O(N/z_0+\sqrt N)$ of them. The remaining $n$ avoid two classes modulo every such $q\in(z_0,\sqrt N]$ with $q\nmid h$; the classes are distinct because $q\ge5$. These primes have density $\frac34$. Brun's sieve in dimension $\frac32$ gives $\ll N(\log z_0/\log N)^{3/2}$ uniformly in $h$. Summing over $|h|\le H_N=O(\ell_N)$ removes $O(N\ell_N(LL)^{3/2}/(\log N)^{3/2})=o(S_\eta(N))$ indices.
- **(W3) First moment.** On the support, $\log|a_2(n)|=\sum_{p^e\|12n+1,\ p\equiv1\,(12)}\log(e+1)$. As in Lemma 2.1 of the Lambert note, with $x=12N+1$,

```math
\sum_{n\le N}\log|a_2(n)|=\sum_{p\equiv1\,(12)}\sum_{e\ge1}\log(e+1)\Bigl(S_{\mathcal S}\bigl(\tfrac x{p^e}\bigr)-S_{\mathcal S}\bigl(\tfrac x{p^{e+1}}\bigr)\Bigr)=\Bigl(\frac{\log2}4+o(1)\Bigr)S_\eta(N)\,LL .
```

  The weight is $(1-\log p/\log x)^{-3/4}$, which is integrable. Mertens in the class $1\bmod12$ gives $\sum_{p\equiv1\,(12),\,p\le y}1/p=\frac14\log\log y+O(1)$. The lower tail follows from Rankin with $z^{\omega_{1(12)}(12n+1)}$, exactly as in Lemma 2.2 there.
- **Valuations.** For $b=2^k$ the remainder is $U_b\le2^{k-1}\mathrm{odd}(|a_2|)$, and $\sum_{n\le N}\mathrm{odd}(|a_2(n)|)\ll N/(\log N)^{3/4}$ by Shiu. For $b$ not a power of $2$ and an odd prime $q\mid b$, $q\mid e+1$ forces $e\ge2$, so $\sum v_q(|a_2(n)|)=O(S_\eta(N))$.

Hence $\omega=0$ for $b=2^k$, and $\omega=\frac{\log2/4}{3/4}=\frac{\log2}3=0.2310<1$ otherwise. With $\lambda_N=\frac34\ell_N+O(1)$ and $\rho_N\sim C_\eta(\log N)^{-3/4}$, Theorem 1 gives $1-D_N\sim(1+\omega)\rho_N\lambda_N$, which is the statement. ∎

### 1.4 Signs, cancellation and collisions

Theorem 1 never uses positivity. For the record:

- **Upper bound.** Phase 20 Theorem 2.2 charges every source its width $u(n)$ (computed from $|U|$) plus $L$. Cancellation within a fiber $C(t)$ can only shorten the union, so signed tails never hurt the upper bound.
- **Lower bound.** For a good source, (G2) excludes every other source within $H_N$ on **both** sides. So the fiber of $t(n)$ is the single source, $C(t)=U(n)$ with its sign, and no cancellation or collision is possible. The tail $A(t)=b^{-R}A(t+R)$ is signed. Markov's inequality is applied to $|A|$ through $\sum_s|A(s)|\le\widehat{\mathsf A}_C/(b-1)$ (Phase 20 Lemma 1.3, which is stated for $|a|$).
- **Marking.** Phase 20 Lemma 3.2 holds for $C(t)<0$. In part (1), $C+A$ is at distance $\ge\frac12$ from $b^j\mathbb Z$ whenever $b\nmid C$. In part (2), a negative source places the point $b^{-j}|Y|$ just below $1$, which is near $0$ on the circle.
- **Separation.** Lemma 3.3 is the circle version and treats arcs through $0$ symmetrically.

The script measures this directly: at $N=2^{17}$ the certified Lemma 3.3 lower bound is $0.26$, and the centred-arc upper bound agrees with $1-D_N$ to $5\cdot10^{-5}$ in all three bases. Positive and negative sources concentrate symmetrically about $0$.

| $b$ | $1-D_N$ at $2^{17}$ | ratio to $(W+S\lambda)/N$ | ratio to Theorem A3 |
|---|---|---|---|
| 2 | 0.83191 | 0.950 | 0.820 |
| 3 | 0.78545 | 1.039 | 0.996 |
| 4 | 0.63064 | 1.034 | 1.243 |

Each value is certified to within $b^{-P}$, with digits certified by two carries and the elementary tail $|a_2(m)|\le r_2(24m+2)\le8\sqrt{24m+2}$. The base-3 ratio near $1$ is a coincidence at $LL=2.4$.

## 2. Binary quadratic forms (Track A4)

### 2.1 Arithmetic of $r_Q$

Write $Q=gQ_0$ with $Q_0$ primitive of discriminant $\Delta_0=\Delta/g^2$. Then $r_Q(n)=r_{Q_0}(n/g)$, and the sources of $\Theta_Q(1/b)-1$ sit at positions $n=gj$.

- **(F1) Mass.** $\sum_{n\le X}r_Q(n)=\frac{2\pi}{\sqrt{|\Delta|}}X+O(\sqrt X)$ (Phase 20 Lemma 3).
- **(F2) Pointwise bound.** The number of proper representations of $m$ by a full system of primitive classes of discriminant $\Delta_0$ is at most $w\cdot\#\{t\bmod2m:t^2\equiv\Delta_0\ (4m)\}\le C_{\Delta_0}\,2^{\omega(m)}$ (with equality when $\gcd(m,f)=1$ for $\Delta_0=f^2D_K$). Summing over $k^2\mid m$ gives $r_{Q_0}(m)\le C\tau(m)^2=m^{o(1)}$. More precisely, $r_{Q_0}(m)\le C\,2^{\omega_{\rm split}(m)}\sigma_2(m)$, where $\sigma_2(m)=\prod_{p^e\|m}(\lfloor e/2\rfloor+1)$.
- **(F3) Support.** If $(\Delta_0/p)=-1$, then $Q_0$ is anisotropic modulo $p$, so $v_p(Q_0(x,y))$ is even (Phase 20 Lemma 4). Thus $\operatorname{supp}r_{Q_0}\subseteq M_{\Delta_0}=\{j:v_p(j)\text{ even whenever }(\Delta_0/p)=-1\}$. Bernays (1912) proved $S_{Q_0}(x)\sim C_{Q_0}x/\sqrt{\log x}$, and $C_Q=C_{Q_0}/g$.
- **(F4) Ideals.** For fundamental $\Delta$ and $Q$ in the ideal class $C$, $r_Q(n)=w\,a_C(n)$ with $a_C(n)=\#\{\mathfrak a:N\mathfrak a=n,\ [\mathfrak a]=C\}$. Moreover $a_C=a_{C^{-1}}$ and $\sum_Ca_C=a:=1*\chi_\Delta$.

The script checks (F4) for every $n\le65{,}640$ and seven discriminants. It builds $a_C(n)$ as a product in $\mathbb Z[\mathrm{Cl}]$ of the local factors

- $\sum_{i=0}^e[\mathfrak p]^{2i-e}$ at split $p$;
- $\mathbf 1_{2\mid e}$ at inert $p$;
- $[\mathfrak p]^e$ at ramified $p$,

where each prime ideal class is read off from the form that represents $p$. It then compares the products with lattice-point counts.

### 2.2 The complete lower bound for every $Q$ (Theorem A4(1))

**Proposition 2.1.** For every positive definite integral binary $Q$ and every $b\ge2$,

```math
1-D_N(\Theta_Q(1/b);b)\ \ge\ (1-o(1))\,\frac{S_Q(N)}N\cdot\frac12\log_b\log N .
```

*Proof.* Let $a(n)=r_Q(n)$ for $n\ge1$; the term $r_Q(0)=1$ is an integer and drops out. Put $\rho_N=S_Q(N)/N\asymp(\log N)^{-1/2}$ (Bernays' lower bound), $\lambda_N=\log_b(1/\rho_N)=\frac12\ell_N+O(1)$, $H_V=\lceil2\ell_N\rceil$, $R=\lceil\lambda_N+2\ell_N\rceil$ and $H=R+H_V$. Call $n=gj\le N$ good if (G1)–(G4) of Theorem 1 hold. Condition (G5) is not needed, and the width is not used.

1. **(E1) Displacement.** $b^{V(n)}\le r_Q(n)$. By (F1) and Markov, $\#\{n\le3N:V(n)>H_V\}\le b^{-H_V}\sum_{n\le3N}r_Q(n)\ll N/(\log N)^2$. Also $V(n)\le\log_br_Q(n)=o(\log n)$ by (F2), so $t(n)\ge n/2$.
2. **(E2) Pair sieve.** Two sources $gj<gj'$ within distance $H$ have $h':=j'-j$ with $1\le h'\le H/g\le H$, and $j,j+h'\in M_{\Delta_0}$. Discard the $j\le N/g$ with $q^2\mid j(j+h')$ for some $q>z_0=(\log N)^2$ with $(\Delta_0/q)=-1$; there are at most $2N/z_0+2\sqrt{2N}$ of them. The remaining $j$ avoid the classes $0$ and $-h'$ modulo each such $q\in(z_0,\sqrt N]$ with $q\nmid h'$. These primes have Dirichlet density $\frac12$ and bounded-error Mertens sums. Brun's sieve (Halberstam–Richert Theorem 2.2) in dimension $1$ gives $\ll N\log z_0/\log N$, uniformly in $h'$, because the primes $q\mid h'$ change the Mertens product by a factor $(1-2/z_0)^{-\log_2H}\to1$. Summing over $h'\le H$: $O(N\ell_NLL/\log N)=o(S_Q(N))$.
3. **(E3) Exceptional arrivals.** Each exceptional $n'$ spoils at most $2R+H_V+1$ indices, for a total of $O(N\ell_N/(\log N)^2)$.
4. **(E4) Tails.** For $n$ satisfying (G1)–(G3), $t(n)$ is the only arrival within $R$, and $A(t)=b^{-R}A(t+R)$. With $\sum_{s<M}|A(s)|\le\widehat{\mathsf A}_C(M)/(b-1)\ll M$ by (F1) and $t(n)\ge n/2$,

```math
\#\{|A(t(n))|>\tfrac12\}\ll b^{-R}N\le\rho_NN/(\log N)^2=o(S_Q(N)).
```

Hence $|G|=(1-o(1))S_Q(N)$. For $n\in G$, $b\nmid U(n)=C(t)$ and $|A(t)|\le\frac12$. Phase 20 Lemma 3.2(1) gives $\|x_{t-j}\|\ge b^{-j}/2\ge\eta$ for $1\le j\le\lambda'=\lfloor\log_b(1/(2\eta))\rfloor$. These shifts lie in disjoint arrival-free gaps of length $R\ge\lambda'$. Take

- $\zeta=(\log N)^{-1/2}$;
- $\Delta=|G|(\lambda'-1)/N$;
- $\eta=\zeta+2\rho_N\lambda_N$ (so $\zeta+\Delta<\eta\le\frac12$ directly for all large $N$).

Then $\lambda'=\lambda_N-O(\log\lambda_N)$. By the upper-bound count at $\varepsilon=\zeta$ (Phase 20 Lemma 1 with $L=\lceil2\ell_N\rceil$), at least $N-E_N(\zeta)\ge N(1-O(\ell_N(\log N)^{-1/2}))$ points satisfy $\|x_n\|\le\zeta$. Lemma 3.3 gives $1-D_N\ge\Delta=(1-o(1))\rho_N\lambda_N$. ∎

Proposition 2.1 upgrades Phase 20 Proposition 6, which was an outline, to a complete proof. It uses no multiplicativity and no bound on large $r_Q(n)$ beyond (F1) and (F2). A Rankin bound on large $r_Q$ is needed only for the width term: by (F2) and Shiu, $\sum_{j\in M_{\Delta_0},\,j\le N}(2^{\omega_{\rm split}(j)}\sigma_2(j))^s\ll N(\log N)^{2^{s-1}-1}$ (with $\sigma_2(j)$ from (F2)). Hence $r_{Q_0}(j)\le(\log N)^\theta$ for all but $o(S_Q(N))$ supported $j$, for every fixed $\theta>(\log2)/2$. That is the upper-tail half of the concentration used below.

### 2.3 Class number one and one class per genus (Theorem A4(2), (3))

**Class number one.** If $h(\Delta)=1$ and $\Delta$ is fundamental, then $r_Q=w\,c$ with $c=1*\chi_\Delta$. The proof of Theorem A1 applies verbatim to $w\,c$, because multiplying by the constant $w$ changes $V_b$, $U_b$ and $u_b$ by $O(1)$ (and by nothing on average after the first moment). So $1-D_N\sim C_{\chi_\Delta}/(2\log b)\cdot LL/\sqrt{\log N}$ for $b=2^k$, and $\sim C_{\chi_\Delta}(1+\log2)/(2\log b)\cdot LL/\sqrt{\log N}$ otherwise.

**One class per genus.** If $\Delta$ is fundamental and $h_0=1$, every genus is a single class. All ideals of norm $n$ lie in one genus, so $a_C(n)=a(n)\mathbf 1[n\in\text{genus}(C)]$ exactly, and $r_Q=w\,a\,\mathbf 1_{\rm genus}$. The support of $Q$ is the part of $\operatorname{supp}a$ in one genus. Its counting function is $(1/g+o(1))S_\Delta(x)$: twisting $\mathbf 1_{\operatorname{supp}a}$ by a nontrivial genus character $\psi$ changes the split-prime sum to $\frac12(\log L(s,\chi_{d_1})+\log L(s,\chi_{d_2}))+O(1)$, bounded at $s=1$, so the twisted mean is $O(x/\log x)$. The first moment of $\log a$ over one genus is computed by the decomposition of Lemma 2.1 of the Lambert note. The number of $n=p^em$ in a fixed genus is the genus-restricted count of $m$, which is again asymptotic to $1/g$ of the full count. So it equals $(\frac{\log2}2+o(1))S_Q(N)LL$, and Theorem 1 applies with $\omega\in\{0,\log2\}$ as before. In the script, the two genera of $\Delta=-20$ (and of $\Delta=-24$) partition $\operatorname{supp}(1*\chi_\Delta)$ exactly, and $r_Q(n)\in\{0,\,2a(n)\}$ for every $n\le65{,}640$. The ratios $S_Q/S_\Delta$ are $0.5000/0.5000$ and $0.5002/0.4998$.

### 2.4 Several classes per genus (Theorem A4(4))

**Proposition 2.2 (concentration of $r_Q$).** Let $\Delta$ be fundamental with $h_0>1$, and let $C$ be a class with genus $G$. There is $c>0$ such that for all but $O(S_\Delta(N)(\log N)^{-c})$ integers $n\le N$ in $\operatorname{supp}a$ with genus $G$,

```math
\Bigl|\frac{h_0\,a_C(n)}{a(n)}-1\Bigr|\le(\log N)^{-c}.
```

*Proof.* Orthogonality over the class group $\widehat{\mathrm{Cl}}$ gives

```math
a_C(n)=\frac1h\sum_{\psi\in\widehat{\mathrm{Cl}}}\overline\psi(C)\prod_{p^e\|n}\lambda_\psi(p^e),\qquad
\lambda_\psi(p^e)=\begin{cases}\sum_{i=0}^e\psi(\mathfrak p)^{2i-e}&\text{split},\\ \mathbf 1_{2\mid e}&\text{inert},\\ \psi(\mathfrak p)^e&\text{ramified}.\end{cases}
```

For the $g$ genus characters ($\psi^2=1$), $\lambda_\psi(p^e)=(e+1)\psi(\mathfrak p)^e$. Their total contribution is $\frac gh\,a(n)\mathbf 1[n\in G]=a(n)/h_0$. Every other $\psi$ has $\psi^2\ne1$. At split $p\|n$ with $[\mathfrak p]\notin\ker\psi^2$, $|\lambda_\psi(p)|=2|\cos\arg\psi(\mathfrak p)|\le2\theta_{\rm Cl}$ with $\theta_{\rm Cl}<1$, and always $|\lambda_\psi(p^e)|\le e+1$. Thus

```math
\Bigl|a_C(n)-\frac{a(n)}{h_0}\Bigr|\le a(n)\,\max_{\psi^2\ne1}\theta_{\rm Cl}^{\nu_\psi(n)},\qquad \nu_\psi(n)=\#\{p\|n\ \text{split}:[\mathfrak p]\notin\ker\psi^2\}.
```

Hecke's equidistribution of prime ideals in classes (Chebotarev in the Hilbert class field) gives these primes density $\frac12(1-[\mathrm{Cl}:\ker\psi^2]^{-1})\ge\frac14$, with bounded-error Mertens sums. Rankin with $z^{\nu_\psi}$, as in Lemma 2.2 of the Lambert note, shows $\nu_\psi(n)\ge c_0LL$ outside $O(S_\Delta(N)(\log N)^{-c_1})$ indices. ∎

**Corollaries.**

1. **Bernays.** Almost every $n$ represented by the genus of $Q$ is represented by $Q$: the error is $<1/h_0$, so $a_C(n)>0$. Hence $S_Q(N)\sim S_G(N)\sim(C_{\chi_\Delta}/g)N/\sqrt{\log N}$.
2. **Concentration.** $\log r_Q(n)=\log(w/h_0)+\log a(n)+o(1)$ for almost all $n\in\operatorname{supp}r_Q$. So $r_Q(n)$ concentrates at $2^{\omega_{\rm split}(n)}w/h_0$ times the tight odd factor $\prod_{e_p\ge2}(e_p+1)$. The exponent of $2$ is $\omega_{\rm split}(n)-O(1)$, not a smaller power. For $\Delta=-23$ the script finds $|3a_{C_0}(n)/a(n)-1|\le\frac12$ for $99.5\%$ of the $n\le65{,}640$ with $a(n)\ge8$.
3. **Radix $2^k$ upper value.** If $[\mathfrak p]\in\mathrm{Cl}[2]$, interchanging $\mathfrak p$ and $\bar{\mathfrak p}$ preserves the class, so $2^{m_2(n)}\mid a_C(n)$, where $m_2$ counts the split $p\|n$ with $[\mathfrak p]\in\mathrm{Cl}[2]$. These primes have density $\frac12|\mathrm{Cl}[2]|/h=\frac1{2h_0}$, because $|\mathrm{Cl}[2]|=|\mathrm{Cl}/\mathrm{Cl}^2|=g$. Hence $u_{2^k}(n)\le(\log_2a(n)-m_2(n))/k+O(1)$. The first moment over the genus support, with Chebotarev for the two prime classes, gives $W(N)\le(\frac{(1-h_0^{-1})\log2}{2\log b}+o(1))S_Q(N)LL$. For other $b$ the first moment of $\log a$ gives $\frac{\log2}{2\log b}$.
4. **Lower value.** Proposition 2.1 gives the lower value $1$.

Together with the upper bound of Theorem 1 (which needs only $W(N)$ and $|a(n)|\le n^{o(1)}$) and Proposition 2.1 for the lower bound, these give Theorem A4(4). The exact constant needs the limiting law of $u_b(n)/\lambda_N$ on the support. Proposition 2.2 supplies it outside radix $2^k$ provided $V_b(n)=o(LL)$ for almost all $n$:

**Hypothesis $(\mathrm V_q)$.** For an odd prime $q\mid b$, $v_q(a_C(n))=o(\log\log N)$ for almost all $n\in\operatorname{supp}r_Q$.

Under $(\mathrm V_q)$ the constant is $1+\log2$ for every $b$ divisible by $q$. In radix $2^k$ the constant depends on $v_2(a_C(n))-m_2(n)$, which is governed by the arithmetic of the group-ring products. §2.5 settles the first case completely.

### 2.5 Class group $\mathbb Z/3$ (Theorem A4(5))

Let $\mathrm{Cl}(\Delta)\cong\mathbb Z/3$ with $\Delta$ fundamental. The discriminants are $-\Delta\in\{23,31,59,83,107,139,211,283,307,331,379,499,547,643,883,907\}$, all prime, so $g=1$, $h_0=3$, and the ramified ideal $(\sqrt\Delta)$ is principal. Split primes are **principal** ($[\mathfrak p]=1$, density $\frac16$) or **nonprincipal** ($[\mathfrak p]=\gamma^{\pm1}$, density $\frac13$). For $\Delta=-23$, $p=2,3,13,29,31,\ldots$ are nonprincipal and $59,101,167,\ldots$ are principal. Call $n\in\operatorname{supp}a$ of **J-type** if some nonprincipal split $p$ has $v_p(n)\equiv2\pmod3$. Let $s(n)=\prod_{p^e\|n,\ p\text{ principal split}}(e+1)$ and $P(n)=\prod_{p^e\|n,\ p\text{ nonprincipal split}}(e+1)$, so $a(n)=s(n)P(n)$.

**Lemma 2.3 (exact structure).** For every $n\in\operatorname{supp}a$ and every class $C$:

1. if $n$ is of J-type, $a_C(n)=a(n)/3$;
2. otherwise $3a_C(n)=s(n)\,(P(n)+\beta)$ with $\beta=\beta(n,C)\in\{\pm1,\pm2\}$ (specifically $\beta\in\{\pm2\}$ for $C=1$ and $\beta\in\{\pm1\}$ for $C\ne1$); in particular $v_2(3a_C(n)/s(n))\le1$ whenever $4\mid P(n)$.

*Proof.* Take the character $\psi(\gamma)=\omega=e^{2\pi i/3}$. At a nonprincipal split $p^e$, $\lambda_\psi(p^e)=\sum_{i=0}^e\omega^{\pm(2i-e)}$ vanishes iff $3\mid e+1$, and otherwise equals $(-1)^{e\bmod3}\in\{\pm1\}$. At principal split primes $\lambda_\psi=e+1$, and at inert or ramified primes it is $0$ or $1$. If some factor vanishes, both nontrivial characters drop out and $a_C=a/3$. Otherwise $\psi(X_n)=s(n)\varepsilon$ with $\varepsilon\in\{\pm1\}$, so $3a_C=a+2\,\mathrm{Re}(\overline\omega^{C}s\varepsilon)=sP+s\beta$ with $\beta=2\varepsilon\,\mathrm{Re}(\overline\omega^C)\in\{\pm2\}$ for $C=1$ and $\in\{\pm1\}$ for $C\ne1$. If $4\mid P$, then $v_2(P+\beta)=v_2(\beta)\le1$. ∎

The script asserts both cases for every $n\le65{,}640$.

**Proof of Theorem A4(5).** We use Theorem 1 in its mixture form ([radix-lambert.md §1, Remark 5](radix-lambert.md#1-the-sub-threshold-width-law)): truncating $G$ by $u(n)\le\lambda_N$ (which discards $o(S(N))$ sources when $\mu([0,1))=1$ and guarantees every marked shift satisfies $u(n)+\lambda'-1<2\lambda_N\le R_N$) yields $1-D_N\sim(1+\int x\,d\mu)\rho_N\lambda_N$ whenever $u(n)/\lambda_N\to\mu$ in distribution on $[0,1)$ and $W(N)\le(\int x\,d\mu+o(1))S\lambda_N$.

- **J-types.** The J-type condition is a local condition at nonprincipal split primes. On $\operatorname{supp}a$ the local law at a split $p$ is geometric, $\mathbb P(v_p(n)=e)=(1-\frac1p)p^{-e}$ (Selberg–Delange with finitely many local conditions). So the J-type density is $\pi_J$, given by the stated product. Truncating at $p\le P_0$ costs $O(1/P_0)$.
- **Radix $2^k$.** For J-types, $a_C=a/3$ and $v_2(a_C)=v_2(a)$, so $u_{2^k}=O(1+\log\mathrm{odd}(a))$, which has bounded mean. For every non-J-type $n$, $s(n)\mid 3a_C(n)$ gives $v_2(r_Q(n))\ge v_2(s(n))$, so $u_{2^k}\le(\log_2P(n)+\log_2\mathrm{odd}(s(n)))/k+O(1)$ unconditionally, with equality up to $O(1)$ whenever $4\mid P(n)$ (which holds for all but $o(S)$ non-J indices by Rankin on $M'$). Here $\log_2P(n)=M'(n)+O(\text{tight})$, where $M'$ counts the nonprincipal split $p\|n$. Since the non-J set $\mathcal N$ is itself multiplicative ($n=p^em\in\mathcal N\iff m\in\mathcal N$ for nonprincipal split $p$ and $e\not\equiv2\pmod3$) with $S_{\mathcal N}(x)\sim(1-\pi_J)C_{\chi_\Delta}x/\sqrt{\log x}$, Lemma 2.1's prime-power decomposition restricted to $\mathcal N$, together with Chebotarev and Rankin (lower tail), shows $M'/LL\to\frac13$ in $L^1$ on $\mathcal N$. So $\mu=\pi_J\delta_0+(1-\pi_J)\delta_{\frac23\log2}$, with mean $\frac23(1-\pi_J)\log2<1$.
- **Other radices.** By Lemma 2.3, $\log_ba_C=\log_ba-\log_b3+O(1)$ in both cases. For an odd prime $q\mid b$: for J-types $v_q(a_C)\le v_q(a)$, which has bounded mean (Lemma 2.3 of the Lambert note). For non-J-types, $v_q(a_C)=v_q(s)+v_q(P+\beta)-v_q(3)$. Write $P=2^{M'}P_1$, where $P_1$ is tight. Fix any $\varepsilon>0$, and choose $P_0(\varepsilon)$ and $K(\varepsilon)$ so that $\mathbb P(P_1>P_0)+\mathbb P(|M'-\frac13LL|>K\sqrt{LL})<\frac23\varepsilon$ (using tightness of $P_1$ and the Rankin Gaussian tail bound on $M'$). For any fixed $P_1\le P_0$ and $\beta\in\{\pm1,\pm2\}$: if $q\mid P_1$ then $q\nmid(P+\beta)$ directly, so $v_q(P+\beta)=0$; if $q\nmid P_1$, then $q^H\mid 2^{M'}P_1+\beta$ confines $M'$ to at most one residue class modulo $d_H=\mathrm{ord}_{q^H}(2)\gg_q q^H$. Inside the window $|M'-\frac13LL|\le K\sqrt{LL}$ there are at most $\frac{2K\sqrt{LL}}{d_H}+1$ integers in that class, and the Sathe–Selberg local law (valid for the Chebotarev set of nonprincipal split primes in the Hilbert class field, or the elementary Hardy–Ramanujan bound of [radix-lambert.md §4.1](radix-lambert.md#41-the-mechanism)) gives $\mathbb P(M'=m)\ll(LL)^{-1/2}$ uniformly in $m$. Summing over the at most $4P_0$ pairs $(P_1,\beta)$ yields
  $$\mathbb P\bigl(v_q(P+\beta)\ge H\bigr)\ \le\ \frac{2\varepsilon}3+O_q\!\left(P_0\Bigl(\frac{K}{q^H}+\frac1{\sqrt{LL}}\Bigr)\right)<\varepsilon$$
  for $H\ge H_0(\varepsilon)$ and all large $N$. Thus $V_b$ is tight, $(\mathrm V_q)$ holds, and $\mu=\delta_{\log2}$.

Theorem 1 (mixture form) now gives both constants. ∎

For $\Delta=-23$:

- $1-\pi_J=0.78363742\ldots$, $\pi_J=0.21636258\ldots$, and $1+\frac23(1-\pi_J)\log2=1.36211738\ldots$ (computed to $p\le5\cdot10^6$; `scripts/phase21_radix.py` truncates at $p\le65{,}640$, giving `0.783638` / `0.216362` / `1.362118`);
- the J-type fraction of $\operatorname{supp}a$ up to $65{,}640$ is $0.2350$, against $\pi_J=0.2164$; on $\operatorname{supp}r_{x^2+xy+6y^2}$ it is $0.3124$, because the principal form misses many non-J integers at finite height;
- the Bernays ratios are $S_Q/S_\Delta=0.752$ for $x^2+xy+6y^2$ and $0.922$ for $2x^2+xy+3y^2$, so the convergence to $1$ is slow.

### 2.6 Certified discrepancies

At $N=2^{16}$, certified to within $b^{-P}$ (tail $r_Q(m)\le2w\sqrt m$). Each ratio is to the conjectured or proved constant of Theorem A4 for that radix. For $\Delta=-23$ in radix $2$ the constant uses the factor $1.3621$.

| $\Delta$ | $Q$ | $C_Q$ | $1-D_N$, $b=2$ | ratio | $1-D_N$, $b=3$ | ratio |
|---|---|---|---|---|---|---|
| $-3$ | $x^2+xy+y^2$ | 0.638909 | 0.76493 | 2.297 | 0.62071 | 1.745 |
| $-4$ | $x^2+y^2$ | 0.764224 | 0.60633 | 1.522 | 0.76640 | 1.801 |
| $-7$ | $x^2+xy+2y^2$ | 0.724720 | 0.64584 | 1.710 | 0.69296 | 1.717 |
| $-8$ | $x^2+2y^2$ | 0.872888 | 0.67034 | 1.474 | 0.73019 | 1.503 |
| $-20$ | $x^2+5y^2$ | 0.535180 | 0.52566 | 1.885 | 0.56665 | 1.902 |
| $-20$ | $2x^2+2xy+3y^2$ | 0.535180 | 0.52506 | 1.882 | 0.56731 | 1.904 |
| $-24$ | $x^2+6y^2$ | 0.558357 | 0.52910 | 1.818 | 0.57888 | 1.862 |
| $-24$ | $2x^2+3y^2$ | 0.558357 | 0.52755 | 1.813 | 0.58121 | 1.870 |
| $-23$ | $x^2+xy+6y^2$ | 0.841512 | 0.56932 | 0.953 | 0.59584 | 1.272 |
| $-23$ | $2x^2+xy+3y^2$ | 0.841512 | 0.66926 | 1.120 | 0.63222 | 1.349 |

Nineteen of the 20 ratios drift towards $1$ between $N=2^{14}$ and $2^{16}$ (the exception is $\Delta=-23$, $Q=x^2+xy+6y^2$, $b=2$, which moves from $0.984$ to $0.953$ because $S_Q/S_\Delta=0.752$ at finite height). They are finite measurements at $LL\le2.41$ and do not test the constants. The two forms of each idoneal discriminant agree to $10^{-3}$, as the exact identity $r_Q=w\,a\,\mathbf 1_{\rm genus}$ and the equidistribution of genera predict. The two forms of $\Delta=-23$ differ at this height because the principal form misses many integers in its genus.

## 3. Verification

```sh
python -B scripts/phase21_radix.py
```

Sections A3 and A4 of the script:

- compute $a_2(n)$ to $10^6$ and verify the criterion for every $n\le10^6$;
- compute $C_\eta$ and its second-order coefficient. The method is checked by reproducing Shanks's constant, and the two-term law is checked against $S_\eta(N)$ at six cutoffs, with relative error below $1.5\%$ from $N=10^4$ and below $0.6\%$ at $10^6$;
- certify discrepancies of $E_b^2$ in bases 2, 3, 4 at $N\le2^{17}$;
- check (F4) for seven discriminants, the idoneal genus partition, Lemma 2.3 for $\Delta=-23$, and $\pi_J$;
- certify 20 form-radix discrepancies.

The whole script runs in about 40 s with about 125,000 assertions and exits 0.

## 4. Status

- **Paper proofs:** Theorem A3 (granting the eigenform input of Phase 20 Theorem 6, verified numerically to $10^6$); Proposition 2.1 (complete, every $Q$); Theorem A4(2), (3); Proposition 2.2 with its corollaries, giving Theorem A4(4); Lemma 2.3 and Theorem A4(5).
- **Conditional:** the exact constant outside radix $2^k$ for general $h_0>1$, under $(\mathrm V_q)$.
- **Open:** the exact radix-$2^k$ constant for class groups other than $\mathbb Z/3$ and those with $h_0=1$; it depends on $v_2$ of the group-ring counts $a_C(n)$ beyond the $\mathrm{Cl}[2]$ flips. Also open are imprimitive and non-fundamental exact constants beyond the order and the lower value of Proposition 2.1.
- **Inputs:** listed in the scope paragraph. The kernel-verified Lean finite core in [radix-lambert.md §6](radix-lambert.md#6-kernel-verified-lean-finite-core) (`NormalityChecker/RadixWidthLaw.lean`) covers the finite steps used here. The group-ring identity of Lemma 2.3 is a further finite statement suitable for Lean (`ZMod 3`-graded products over prime powers).
