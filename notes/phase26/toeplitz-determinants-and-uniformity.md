# Toeplitz Determinants, Positivity and Quantitative Uniformity

Phase 26, Track A (A1–A7). Companion certificate script: [`scripts/phase26_toeplitz_uniformity.py`](../../scripts/phase26_toeplitz_uniformity.py) (standard library only; `python -B scripts/phase26_toeplitz_uniformity.py` exits with code `0` in about 7 s on Windows, passing **77,250 assertions**: **77,052 `[exact]`** (Python integers, `fractions.Fraction`, exact Gaussian rationals $\mathbb{Q}(i)$ and exact cyclotomic rings $\mathbb{Z}[x]/\Phi_Q$) and **198 `[finite]`** (floating point, isolated in the final section)).

**Scope, evidence and benchmark disclaimer.**

- Every theorem below carries one of the evidence labels `Paper proof`, `Finite certificate`, `External input`, `Conditional`, `Open`. No result in this note is `Kernel-verified`; §1.6 gives uncompiled Lean 4 statements for Track H.
- Every `[exact]` assertion in the script is a finite certificate: either a regression instance of a general identity or inequality proved in the text, or a complete finite verification of a finite claim. **No floating-point number appears in any `[exact]` assertion.**
- The `[finite]` table in §12 is a **finite measurement only**. It is never used in a proof and never supports an asymptotic statement.
- Any cross-model review of this note is **not** independent human peer review.
- **Benchmark stability.** Nothing here changes the status of any constant in the fixed roster `BC-01`…`BC-50`. In particular $D^+(\ln 2;2)<1$ remains **Open**. §6 and §7 give an exact reformulation of that target and a limitation theorem; neither is progress on the target itself.
- **Prior repository art.** The binary statement "$D^+(x;2)=1$ iff $\limsup_N|S_N(1)|=1$", with a 0.9997 threshold, is Phase 23 Proposition 5.1 ([`GF-35`](../../docs/results.md#gf-35), [classical-correlations-and-log2.md](../phase23/classical-correlations-and-log2.md)). Theorem 6.2 here extends it to every radix $b\ge2$ (whose $T_b$ has $b-1$ fixed points), adds the 2×2-determinant and fixed-dimension formulations, and gives a sharper explicit converse.

---

## Results at a glance

| ID | Result | Evidence label | External inputs | Objectives |
| --- | --- | --- | --- | --- |
| **A1.1** | Sharp Gram inequality $\det G_{N,r}(h)\le(1-\lvert S_N(h)\rvert^2)^{r-1}$ for every $r\ge1$, including singular $G$. Equality holds iff $S_N(kh)=S_N(h)^k$ for all $0\le k<r$. This covers both the rank-one case $\lvert S\rvert=1$ and nondegenerate cases such as $G=I$ (§1.2) | Paper proof; Finite certificate | None | Obj. 3, 4 |
| **A1.2** | Verblunsky factorization $\det G_{N,r}=\prod_{k=1}^{r-1}(1-\lvert\alpha_k\rvert^2)^{r-k}$, proved from the orbit vectors by a shift isometry and an antiunitary flip. Consequences: the Burg upper bounds, the normalized root $(\det G_{N,r})^{1/r}$ is **nonincreasing in $r$**, and Hadamard–Fischer with a remainder block (§1.3) | Paper proof; Finite certificate | None | Obj. 3 |
| **A1.3** | Classification of extensions. Several coefficients: stronger, sharp (Burg). Different $h$: asymptotically **equivalent**. Polynomial combinations: congruent, so **equivalent**. Multilevel Toeplitz on $\mathbb{T}^d$: **genuinely stronger**, since 1-D projections lose joint singularity. Time-shift ("multiple related radices") Gram: **genuinely different**, measuring linear unpredictability (§1.5) | Paper proof; External input (Helson–Lowdenslager, Szegő) for two upper-direction statements | Helson–Lowdenslager (1958) | Obj. 3, 4 |
| **A2** | **Determinant-to-uniformity transfer.** If $r(N)\to\infty$ and $\liminf(\det G_{N,r(N)}(h))^{1/r(N)}\ge c>0$, then every $\mu\in C_b(x)$ satisfies $\mu\ge c\lambda$. Hence $D^+(x;b)\le1-c$, $\liminf_N f_w(N)\ge c\,b^{-L}$, and $c=1$ gives normality. The proof includes a **self-contained proof of the constant-density case of the Szegő–Kolmogorov–Krein theorem**, the only case needed (§2) | Paper proof | Standard measure theory only (general Szegő theorem cited, not used) | Obj. 1, 3 |
| **A2.6** | For $T_b$-invariant $\mu$: $a(\mu)=\mu(\mathcal N_b)$, the $\mu$-mass of the base-$b$ normal numbers (§2.6) | Paper proof | Borel's normal number theorem | Obj. 3 |
| **A3** | **Optimal-rate characterization** $\sup_{r(N)\to\infty,\ r(N)\le N}\liminf_N(\det G_{N,r(N)}(h))^{1/r(N)}=a_*:=\inf_{\mu\in C_b(x)}a(\mu)$. The supremum is attained, and every slower schedule tending to $\infty$ is also optimal. The value $a_*$ does not depend on $h$. $a_*>0$ is **strictly stronger** than $D^+<1$: for biased Bernoulli $p=1/3$, $D(\mu_{1/3})\in[0.23906,0.24702]$ while $a_*=0$ (§3) | Paper proof; Finite certificate | Birkhoff (generic points) | Obj. 3, 4 |
| **A3.4** | Non-effectivity. $\{x\in\mathbb{R}:a_*(x)=1\}=\mathcal N_b+\mathbb{Z}$ is $\Pi^0_3$-complete in the Borel hierarchy. Recognizing $a_*=1$ on digit-oracle program codes is neither computable, nor c.e., nor co-c.e. **No algorithm maps a program $e$ for $x_e$ to an optimal schedule $r_e$**: a Kleene-recursion-theorem diagonalization of the de Bruijn construction defeats every candidate algorithm on a normal number (§3.4) | Paper proof; External input | Ki–Linton (1994); `AC-11` (registered for $b=2$; the transfer to $b\ge2$ is a paper deduction); Kleene's recursion theorem (standard) | Obj. 4 |
| **A4** | $\det((1-\alpha)I_r+\alpha J_r)=(1-\alpha)^{r-1}(1+(r-1)\alpha)$ for every $\alpha$, including negative $\alpha$. Sharpness of A2 for **every** $c\in[0,1]$ is unconditional and self-contained, via an explicit Champernowne–zero-run construction. The reciprocal witnesses of `GF-45` give an arithmetic realization, used as an external input. Ten controls are analysed (§4) | Paper proof; Finite certificate; External input (`GF-45` witnesses only) | `GF-45` (registered `Paper proof`; Phase 26 Audit III passed, 0 Critical, 0 Major) | Obj. 3 |
| **A5.1** | **Exact Koksma constant**: $\lvert S_N(h)\rvert\le2\lvert h\rvert D_N$ (extreme) and $\le4\lvert h\rvert D_N^*$ (star). The constant $2$ is sharp: an exact certificate gives ratio $>1.957$ for $h=1,2,3$. The bound $2\pi\lvert h\rvert D_N$ is valid but not sharp (§5.1) | Paper proof; Finite certificate | None | Obj. 3 |
| **A5.2** | **Linear-in-$r$ Toeplitz bound** $\lVert G_{N,r}(h)-I\rVert\le\pi\lvert h\rvert(r-1)D_N$, against the quadratic row-sum bound $\lvert h\rvert D_N r(r-1)$. Two-sided Fourier-energy log-determinant estimate when $\lVert G-I\rVert<1$; outside that regime the converse fails (explicit counterexample, Corollary 5.4). For Stoneham numbers (`ST-28`) the determinant root tends to 1 for **every** $r(N)=o(N^{1/2}(1+\log N)^{-2})$, improving $\lfloor N^{1/5}\rfloor$. This is a control deduced from known normality, not a new proof (§5.2–5.4) | Paper proof; External input `ST-28` | `ST-28` (Vandehey) | Obj. 1 (rates), 3 |
| **A5.5** | **Random-point law** $\mathbb E\det G_{N,r}=\prod_{j<r}(1-j/N)$ for i.i.d. uniform points, exact on $\mu_Q$ when $Q\ge r$. Also $\mathbb E\log\det G_{N,N}=-N\log N$ (§5.5) | Paper proof; Finite certificate | None | Obj. 3, 4 |
| **A6.1** | Regularized root $\lim_m(\det T_m((1-t)\nu+t\lambda))^{1/m}=t+(1-t)a(\mu)$. This is affine in $a$, so regularization carries **no new information** asymptotically. Lipschitz stability with constant $1/t$ (§6.1) | Paper proof; Finite certificate | None | Obj. 3, 4 |
| **A6.2** | **Fixed-dimension characterization in every radix**: $D^+(x;b)<1\iff\liminf_N\det G_{N,2}(1)>0\iff\limsup_N\lvert S_N(1)\rvert<1$. Explicit per-$N$ two-sided inequalities. $x\in K_b\iff\lvert S_N(1)\rvert\to1$. For $\ln2$: $\limsup\lvert S_N(1)\rvert\le0.99979995$ suffices for $D^+\le0.9999$, and $D^+\le0.9999$ forces $\limsup\lvert S_N(1)\rvert\le1-16/(27\cdot10^{12})$ (§6.2) | Paper proof; Finite certificate | None (extends Phase 23 Prop. 5.1) | Obj. 3, 4 |
| **A6.3** | Fixed-dimension hierarchy: $\liminf_N\det G_{N,m}(1)>0$ iff no limit measure is supported on fewer than $m$ points (§6.3) | Paper proof; Finite certificate | None | Obj. 3 |
| **A6.4** | Finite interval-mass certificate: $\lambda_{\min}(G_{N,r}(1))\ge\gamma$ implies $D_N\le1-\gamma+2\sqrt{\gamma/r}$, for every $N$ (§6.4) | Paper proof; Finite certificate | None | Obj. 3 |
| **A7.1** | Cauchy–Binet identity. $N^r\det G$ is a totally nonnegative algebraic integer for rational orbits. **Vandermonde divisibility** $p^{r(r-1)}\mid\mathrm{Norm}(N^r\det G)$ for $Q=p$. Galois-averaged lower bound. Uniform-roots identity $\sum_{\lvert I\rvert=r}\lvert V_I\rvert^2=Q^r$ (§7.1–7.2) | Paper proof; Finite certificate | None | Obj. 4 |
| **A7.3** | **Separation-cost barrier**: separation-based lower bounds cost $r(r-1)\log(Q/4)$ against the net budget $r\log(e/(rc))$ left after the factor $N^r$ cancels $N^{-r}$. For the $\ln2$ BBP models $\log Q_N\sim N$, so **only $r=1$ survives**, and the whole difficulty sits in the 2×2 determinant, i.e. the Weyl sum (§7.3, §7.6) | Paper proof | Prime number theorem (size of $\mathrm{lcm}$) | Obj. 4 |
| **A7.4** | **Rank-only and denominator-only countermodels**. Every irrational $x$, including $\sum b^{-k!}\in K_b$, has full-rank Gram matrices with every Cauchy–Binet term positive. Distinct clustered rational configurations with growing denominators have $\det G_{N,2}<2/N^2$ (§7.4–7.5) | Paper proof; Finite certificate | None | Obj. 4 |

---

## 0. Definitions and conventions

Throughout, $b\ge2$ is an integer radix, $x\in\mathbb{R}$, $h\in\mathbb{Z}\setminus\{0\}$, $e(t)=\exp(2\pi i t)$, $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ and $\lambda$ is Lebesgue (Haar) probability measure on $\mathbb{T}$.

- **Orbit and orbit measures.** $t_n=\{b^nx\}$, $T_b(t)=bt \bmod 1$, and $\mu_N=\frac1N\sum_{0\le n<N}\delta_{t_n}$. $C_b(x)$ is the set of weak-$*$ subsequential limits of $(\mu_N)$. It is nonempty and compact because the probability measures on $\mathbb{T}$ form a weak-$*$ compact set.
- **Weyl sums and orbit Gram matrices.** $S_N(h)=\frac1N\sum_{n<N}e(hb^nx)=\int e(ht)\,d\mu_N(t)$. Put $z_n=e(ht_n)$ and $v_j=N^{-1/2}(z_n^{\,j})_{n<N}\in\mathbb{C}^N$, with $\langle u,v\rangle=\sum_n u_n\overline{v_n}$. Then
  $$G_{N,r}(h)_{jk}=\langle v_k,v_j\rangle=S_N((k-j)h),\qquad 0\le j,k<r .$$
  So $G_{N,r}(h)$ is a positive semidefinite Hermitian Toeplitz matrix with unit diagonal. $D:=\mathrm{diag}(z_n)$ is unitary and $v_{j+1}=Dv_j$.
- **Toeplitz matrices of measures.** For a finite positive Borel measure $\rho$ on $\mathbb{T}$, $T_m(\rho)_{jk}=\int e((k-j)\theta)\,d\rho(\theta)$ for $0\le j,k<m$, and $D_m(\rho)=\det T_m(\rho)$. For $a\in\mathbb{C}^m$ and $q(\theta)=\sum_k a_ke(k\theta)$,
  $$a^*T_m(\rho)a=\int\lvert q\rvert^2\,d\rho\ge0 .$$
  With $M_h(t)=ht\bmod1$ and $\nu_N=(M_h)_*\mu_N$ we have $G_{N,r}(h)=T_r(\nu_N)$.
- **Gram–Schmidt residuals.** $d_j=\operatorname{dist}(v_j,\operatorname{span}(v_0,\dots,v_{j-1}))^2$, with $d_0=1$. For a measure $\rho$, $d_j(\rho)$ is the same quantity for $v_j=e(j\theta)\in L^2(\rho)$, which equals $\min\{\int\lvert p\rvert^2d\rho: p\text{ monic of degree }j\}$.
- **Discrepancy.** $D_N=D_N(x;b)=\sup_{0\le u<v\le1}\lvert\mu_N([u,v))-(v-u)\rvert$, the repository's extreme discrepancy on half-open intervals. $D_N^*=\sup_{0\le t\le1}\lvert\mu_N([0,t))-t\rvert$, $D^+=\limsup D_N$, $D^-=\liminf D_N$, and $K_b=\{x:D_N\to1\}$. For a probability measure $\rho$, $D(\rho)$ is defined in the same way.
- **Words.** For a word $w$ of length $L$, $I_w=[u_w,u_w+b^{-L})$ is its $b$-adic interval and $f_w(N)=\mu_N(I_w)$ is its frequency among positions $0\le n<N$.
- **Lebesgue component.** By Lebesgue decomposition, $\mu=\mu_{ac}+\mu_s$ with $\mu_{ac}\ll\lambda$ and $\mu_s\perp\lambda$, uniquely. For $T_b$-invariant $\mu$ we prove $\mu_{ac}=a(\mu)\lambda$ (Lemma 2.2), and set $a_*=\inf_{\mu\in C_b(x)}a(\mu)$.
- $\mathcal N_b\subset[0,1)$ is the set of base-$b$ normal numbers.

**Lemma 0.1 (discrepancy conventions; Paper proof).** Put $R(t)=\mu_N([0,t))-t$ on $[0,1]$, so $R(0)=R(1)=0$.

1. $D_N=\sup R-\inf R$.
2. $D_N$ equals the supremum of $\lvert\mu_N(J)-\lambda(J)\rvert$ over half-open **circular** arcs $J$.
3. $D_N^*\le D_N\le2D_N^*$.

*Proof.* (1) $\mu_N([u,v))-(v-u)=R(v)-R(u)$, and $\sup_{u<v}\lvert R(v)-R(u)\rvert=\sup_{u,v}\lvert R(v)-R(u)\rvert=\sup R-\inf R$. (2) The complement of a circular half-open arc in $\mathbb{T}$ is a half-open subinterval of $[0,1)$, and $\mu_N(J)-\lambda(J)=-(\mu_N(J^c)-\lambda(J^c))$. (3) This is immediate from (1) and $R(0)=0$. ∎

---

## 1. Track A1: sharp Gram inequalities and their generalizations

### 1.1 Gram–Schmidt factorization, singular case included

**Lemma 1.1 (Paper proof).** Let $v_0,\dots,v_{r-1}$ ($r\ge1$) be vectors in a complex inner product space, and let $G_{jk}=\langle v_k,v_j\rangle$. Then $\det G=\prod_{j<r}d_j$. Consequently $\det G\ge0$, and $\det G=0$ iff some $d_j=0$ iff the $v_j$ are linearly dependent.

*Proof.* Let $P_j$ be the orthogonal projection onto $W_j=\operatorname{span}(v_0,\dots,v_{j-1})$ ($W_0=0$) and put $u_j=v_j-P_jv_j$.

- The $u_j$ are pairwise orthogonal, since $u_i\in W_j$ and $u_j\perp W_j$ for $i<j$.
- By induction, $W_j=\operatorname{span}(u_0,\dots,u_{j-1})$.
- Hence $P_jv_j=\sum_{i<j,\,u_i\neq0}\frac{\langle v_j,u_i\rangle}{\lVert u_i\rVert^2}u_i$. Zero vectors $u_i$ are simply omitted, which is the singular case.

So $V=UT$ with $V=[v_0\cdots v_{r-1}]$, $U=[u_0\cdots u_{r-1}]$ and $T$ unit upper triangular. Then $G=V^*V=T^*\operatorname{diag}(\lVert u_j\rVert^2)\,T$, and $\det G=\lvert\det T\rvert^2\prod_j\lVert u_j\rVert^2=\prod_jd_j$. No invertibility is used. ∎

### 1.2 The sharp single-coefficient inequality

**Theorem 1.2 (A1.1; Paper proof, Finite certificate).** For every $N\ge1$, $r\ge1$ and nonzero $h$,
$$\det G_{N,r}(h)\le\bigl(1-\lvert S_N(h)\rvert^2\bigr)^{r-1}\le\bigl(1-\lvert S_N(h)\rvert^2\bigr)^{\lfloor r/2\rfloor},$$
with the convention $0^0=1$. Equality holds in the first inequality **iff** $S_N(kh)=S_N(h)^k$ for all $0\le k<r$. In particular:

- $r\in\{1,2\}$: equality always holds, since $\det G_{N,2}=1-\lvert S_N(h)\rvert^2$.
- $\lvert S_N(h)\rvert=1$: all $z_n$ are equal, $G$ has rank one, and both sides vanish for $r\ge2$.
- $\lvert S_N(h)\rvert<1$, $r\ge3$: equality forces the moments to be geometric, and then $\det G>0$. Equality does occur, for example when the $z_n$ are equidistributed on the $m$-th roots of unity and $r\le m$; then $G=I$ and $S=0$.

For $r\ge3$ and $0<\lvert S\rvert<1$ the new exponent $r-1$ is strictly larger than $\lfloor r/2\rfloor$.

*Proof.* By Lemma 1.1, $\det G=\prod_{j<r}d_j$ with $d_0=\lVert v_0\rVert^2=1$. For $j\ge1$, $W_j\supseteq\operatorname{span}(v_{j-1})$, so
$$d_j\le\operatorname{dist}(v_j,\mathbb{C}v_{j-1})^2=\lVert v_j\rVert^2-\lvert\langle v_j,v_{j-1}\rangle\rvert^2=1-\lvert S_N(h)\rvert^2.$$
Here $\langle v_j,v_{j-1}\rangle=\langle Dv_{j-1},v_{j-1}\rangle=\sum_n\lvert v_{j-1,n}\rvert^2z_n=S_N(h)$ for every $j$. This proves the inequality, including the singular case. For $r=1$ both sides equal $1$. The second inequality holds because $r-1\ge\lfloor r/2\rfloor$ and the base lies in $[0,1]$.

*Equality.* If $\lvert S\rvert=1$, then $\lvert\frac1N\sum z_n\rvert=1$ with $\lvert z_n\rvert=1$ forces all $z_n$ to be equal, so $S_N(kh)=z^k=S^k$ and both sides are $0$ for $r\ge2$. Now let $\lvert S\rvert<1$ and $r\ge2$.

- If equality holds, then every $d_j=1-\lvert S\rvert^2>0$. So for each $j\ge1$ the residual $v_j-Sv_{j-1}$ after projecting on $v_{j-1}$ is already orthogonal to $W_j$. Pairing with $v_0$ gives $S_N(jh)=S\cdot S_N((j-1)h)$, hence $S_N(jh)=S^j$ by induction.
- Conversely, if $S_N(kh)=S^k$ for $k<r$, then $\langle v_j-Sv_{j-1},v_i\rangle=S^{j-i}-S\cdot S^{j-1-i}=0$ for $i\le j-1$. So $d_j=1-\lvert S\rvert^2$ for every $j\ge1$. ∎

The script verifies the inequality, the Gram–Schmidt factorization, residual monotonicity and the equality characterization exactly. It uses 75 configurations of exact rational points of the unit circle, $z=((1-t^2)+2ti)/(1+t^2)$, including $r=1$, rank-one, rank-deficient ($r>\#$points) and $G=I$ cases (section A1, 5,230 `[exact]` assertions).

### 1.3 Verblunsky factorization from the orbit vectors

For $1\le j\le r-1$ put $W'_j=\operatorname{span}(v_1,\dots,v_{j-1})$ ($W'_1=0$), $f_j=v_j-P_{W'_j}v_j$ and $g_j=v_0-P_{W'_j}v_0$. When $d_{j-1}>0$ put $\alpha_j=\langle f_j,g_j\rangle/d_{j-1}$.

**Theorem 1.3 (A1.2; Paper proof, Finite certificate).** Suppose $d_0,\dots,d_{j-1}>0$. Then:

1. $\lVert f_j\rVert^2=\lVert g_j\rVert^2=d_{j-1}$.
2. $d_j=d_{j-1}(1-\lvert\alpha_j\rvert^2)$ and $\lvert\alpha_j\rvert\le1$.
3. $\alpha_1=S_N(h)$.
4. If $\det G_{N,r-1}(h)>0$, then
$$\det G_{N,r}(h)=\prod_{k=1}^{r-1}\bigl(1-\lvert\alpha_k\rvert^2\bigr)^{r-k}.$$
5. If $k$ is the first index with $d_k=0$, then $\lvert\alpha_k\rvert=1$ and $\det G_{N,r}=0$ for all $r>k$.

The $\alpha_k$ agree in modulus with the Verblunsky (Schur, reflection, partial-autocorrelation) coefficients of $\nu_N$. In Simon's indexing these are $\alpha_{k-1}$.

*Proof.*

- *Shift.* $D$ is unitary and maps $(v_0,\dots,v_{j-1})$ onto $(v_1,\dots,v_j)$. So it maps $\operatorname{span}(v_0,\dots,v_{j-2})$ onto $W'_j$, and $\lVert f_j\rVert^2=\operatorname{dist}(v_{j-1},\operatorname{span}(v_0,\dots,v_{j-2}))^2=d_{j-1}$.
- *Antiunitary flip.* $C(u)=D^{j-1}\overline{u}$ is conjugate-linear and norm-preserving, and $C(v_k)=N^{-1/2}(z_n^{j-1}\overline{z_n}^{\,k})=v_{j-1-k}$. Since $C(v_k)=v_{j-1-k}$ for $1\le k\le j-1$, it maps $W'_j=\operatorname{span}(v_1,\dots,v_{j-1})$ onto $\operatorname{span}(v_0,\dots,v_{j-2})$, and it maps $v_0$ to $v_{j-1}$. Distances to subspaces are preserved by such maps, so $\lVert g_j\rVert^2=\operatorname{dist}(v_0,W'_j)^2=\operatorname{dist}(v_{j-1},\operatorname{span}(v_0,\dots,v_{j-2}))^2=d_{j-1}$.
- *Recursion.* $\operatorname{span}(v_0,\dots,v_{j-1})=W'_j\oplus\mathbb{C}g_j$ and $f_j\perp W'_j$. So $d_j=\operatorname{dist}(f_j,\mathbb{C}g_j)^2=\lVert f_j\rVert^2-\lvert\langle f_j,g_j\rangle\rvert^2/\lVert g_j\rVert^2=d_{j-1}(1-\lvert\alpha_j\rvert^2)$. Cauchy–Schwarz gives $\lvert\alpha_j\rvert\le1$.
- *Base case.* For $j=1$: $f_1=v_1$, $g_1=v_0$ and $\alpha_1=\langle v_1,v_0\rangle=S_N(h)$.
- *Product formula.* $d_j=\prod_{k\le j}(1-\lvert\alpha_k\rvert^2)$, and $\det G=\prod_{j<r}d_j$ (Lemma 1.1) gives (4). Statement (5) follows from (2). ∎

**Corollary 1.4 (Burg bound; several specified coefficients; Paper proof).** Let $m\ge1$ and suppose $\det G_{N,m}(h)>0$, i.e. $d_0,\dots,d_{m-1}>0$. Then $\alpha_1,\dots,\alpha_m$ are defined, and they are determined by $S_N(h),\dots,S_N(mh)$. For every $r>m$,
$$\det G_{N,r}(h)\le\prod_{k=1}^{m}\bigl(1-\lvert\alpha_k\rvert^2\bigr)^{r-k},\qquad \bigl(\det G_{N,r}(h)\bigr)^{1/r}\le d_m^{\,(r-m)/r},\qquad d_m=\frac{\det G_{N,m+1}}{\det G_{N,m}} .$$
The second bound holds at the fixed index $N$, uniformly in $r>m$. A limit $r\to\infty$ at fixed $N$ carries no information, because $\det G_{N,r}=0$ for $r>N$ (Proposition 1.6). The asymptotic form belongs to measures: if $\rho$ is a finite positive measure with $D_m(\rho)>0$, then $\limsup_{r\to\infty}D_r(\rho)^{1/r}\le d_m(\rho)=D_{m+1}(\rho)/D_m(\rho)$. When $d_m>0$, equality in the first bound holds iff $\alpha_k=0$ for $m<k<r$, which is Burg's maximum-entropy extension. For $m=1$ the first bound is Theorem 1.2. Using more coefficients gives a genuinely stronger bound.

*Proof.* By Theorem 1.3(2), $d_j=\prod_{k\le j}(1-\lvert\alpha_k\rvert^2)$ for $j\le m$, and $d_j\le d_m$ for $j\ge m$ by Corollary 1.5(1). Hence $\det G_{N,r}=\prod_{j<r}d_j\le\prod_{j\le m}d_j\cdot d_m^{\,r-1-m}=\prod_{k=1}^m(1-\lvert\alpha_k\rvert^2)^{r-k}$. Also $\det G_{N,r}\le\prod_{j<m}d_j\cdot d_m^{\,r-m}\le d_m^{\,r-m}$, since $d_j\le1$. The same computation in $L^2(\rho)$, where $d_j(\rho)$ is again nonincreasing, gives $D_r(\rho)^{1/r}\le\bigl(\prod_{j<m}d_j(\rho)\bigr)^{1/r}d_m(\rho)^{(r-m)/r}\to d_m(\rho)$. ∎

**Corollary 1.5 (monotone normalized root; Hadamard–Fischer with remainder; Paper proof, Finite certificate).**

1. $d_0\ge d_1\ge\cdots$, since $d_j\le\operatorname{dist}(v_j,W'_j)^2=d_{j-1}$ by the shift.
2. $(\det G_{N,r})^{1/r}\le(\det G_{N,m})^{1/m}$ for $1\le m\le r$. Indeed $\frac1r\log\det G_{N,r}$ is the average of the first $r$ terms of a nonincreasing sequence in $[-\infty,0]$.
3. With $r=qm+s$ and $0\le s<m$,
$$\det G_{N,r}\le(\det G_{N,m})^{q}\det G_{N,s}\le(\det G_{N,m})^{\lfloor r/m\rfloor} .$$
   The remainder block $G_{N,s}$ has unit diagonal, so $\det G_{N,s}\le1$ by Hadamard's inequality ($\det G_{N,0}=1$).

*Proof of 3.* The consecutive diagonal blocks are principal submatrices on index intervals, hence equal to $G_{N,m}$ (or $G_{N,s}$) by the Toeplitz structure. For $j$ in a block starting at $p$, $d_j\le\operatorname{dist}(v_j,\operatorname{span}(v_p,\dots,v_{j-1}))^2=d_{j-p}$ by the shift. Multiplying over blocks gives the claim. This is Fischer's inequality in Gram form. ∎

Statement 2 is the more convenient tool in §2, because it removes all remainder bookkeeping.

### 1.4 Rank and nonvanishing

**Proposition 1.6 (Paper proof, Finite certificate).** $\operatorname{rank}G_{N,r}(h)=\min(r,\#\{z_n:n<N\})$. Hence:

- $\det G_{N,r}(h)>0$ iff the orbit contains at least $r$ distinct points $z_n$.
- For irrational $x$, all $z_n$ are distinct, because $h(b^n-b^m)x\notin\mathbb{Z}$ for $n\ne m$. So $\det G_{N,r}(h)>0$ for **every** $r\le N$.
- For rational $x$ with preperiod $\pi$ and period $P$, $\det G_{N,r}=0$ whenever $r>\pi+P$.

*Proof.* $G=V^*V$, where $V$ has rows $N^{-1/2}(z_n^{\,j})_{j<r}$. A Vandermonde matrix with distinct nodes has full rank, and repeated rows add no rank. ∎

The script checks this exactly over $\mathbb{Q}(i)$ and over $\mathbb{Z}[\zeta_7]$ and $\mathbb{Z}[\zeta_3]$. For example, $x=1/7$ in base 2 gives $\det G_3\ne0=\det G_4$, and $x=1/3$ gives $\det G_2\ne0=\det G_3$.

### 1.5 Generalizations: which constraints are genuinely stronger

| Extension | Precise form | Verdict |
| --- | --- | --- |
| Several specified coefficients | Corollary 1.4 (Burg) | **Stronger** than A1.1 as soon as $m\ge2$. Sharp. Asymptotically it gives $d_m$ |
| Other single frequencies $h$ | $G_{N,r}(h)=T_r((M_h)_*\mu_N)$ | **Asymptotically equivalent**: the limiting rate $a(\mu)$ does not depend on $h$ (Lemma 2.3). Fixed-dimensional information does depend on $h$ (§6.2) |
| Polynomial combinations of harmonics | Gram matrix of $P_i=\sum_kA_{ki}z^k$ is $A^*GA$, with $\det(A^*GA)=\lvert\det A\rvert^2\det G$ for square $A$ | **Equivalent reformulation**: it is a congruence of the same quadratic form, and $A^*GA\succeq\lambda_{\min}(G)A^*A$ |
| Block Gram matrices over a frequency set $M=\bigcup_\ell h_\ell[0,r)$ | Principal submatrix of $T_R$ | Arithmetic progressions $M$: **equivalent** to Toeplitz. Lacunary $M$: see the next row |
| Multiple related radices / time shifts | $H_r(\mu;h)_{jk}=\int e(h(b^k-b^j)t)\,d\mu$ (Proposition 1.8) | **Genuinely different and incomparable**: measures linear unpredictability. Positive for mixing singular measures (biased Bernoulli), zero for atomic ones |
| Joint distributions of polynomial images; empirical measures on $\mathbb{T}^d$ | Multilevel Toeplitz $T_{[0,r)^d}$ (Proposition 1.7) | **Genuinely stronger** than every 1-D projection, which can turn a singular joint measure into Lebesgue measure |

**Proposition 1.7 (multilevel Toeplitz on $\mathbb{T}^d$).** Let $\boldsymbol t_n=(\{b^nx_1\},\dots,\{b^nx_d\})$ and let $\mu$ be a limit of the empirical measures. Write $T_\Lambda(\mu)_{\boldsymbol j\boldsymbol k}=\int e((\boldsymbol k-\boldsymbol j)\cdot\boldsymbol\theta)\,d\mu$ for $\boldsymbol j,\boldsymbol k\in\Lambda_r=[0,r)^d$.

1. *(Paper proof.)* $\mu$ is invariant under the diagonal map $T_b^{\times d}$. Its absolutely continuous part is $a(\mu)\lambda_d$, by the proof of Lemma 2.2 with Riemann–Lebesgue on $\mathbb{Z}^d$.
2. *(Paper proof.)* $T_{\Lambda_r}(\mu)\succeq a(\mu)I$, so $(\det T_{\Lambda_r}(\mu))^{1/r^d}\ge a(\mu)$.
3. *(External input; proof sketch only.)* $\lim_r(\det T_{\Lambda_r}(\mu))^{1/r^d}\le a(\mu)$. This follows from the Helson–Lowdenslager half-space prediction theorem, in which the singular part is irrelevant, together with the observation that for box indices far from the lower boundary the box-restricted prediction error approximates the half-space error. The details are **not** verified here.
4. *(Paper proof.)* Projections lose joint singularity. If $x_1$ is normal and $x_2=0$, then $\mu=\lambda\times\delta_0$ is singular on $\mathbb{T}^2$ ($a=0$), but the 1-D Gram matrix of the frequency vector $(1,0)$ has asymptotic root $1$.
5. *(Paper proof.)* If the $x_i$ satisfy a rational linear relation, for example $x_2=2x_1$, every limit is carried by a proper subtorus, so $a(\mu)=0$ automatically. The multilevel determinant is informative only for families without such relations, for example $(x,x^2)$.

**Proposition 1.8 (time-shift Gram matrices; Paper proof, External input for item 5).** For $T_b$-invariant $\mu$ put $\gamma(m)=\int e(h(b^m-1)t)\,d\mu$ for $m\ge0$ and $\gamma(-m)=\overline{\gamma(m)}$.

1. $H_r(\mu;h)=(\gamma(k-j))_{j,k<r}$ is Toeplitz, by invariance. The Koopman map $f\mapsto f\circ T_b$ is an isometry of $L^2(\mu)$, so $\gamma$ is positive definite and $H_r=T_r(\sigma_{\mu,h})$ for a spectral measure $\sigma_{\mu,h}$ (Herglotz).
2. For the orbit, $H_{N,r}(h)_{jk}=\frac1N\sum_{n<N}z_{n+k}\overline{z_{n+j}}$ with $z_m=e(ht_m)$. This is the empirical autocorrelation matrix up to $O(r/N)$ boundary terms.
3. $\mu=\lambda$ gives $H_r=I$. A fixed-point Dirac gives rank one. If $\mu$ is supported on $s$ points, $\det H_r=0$ for $r>s$.
4. Biased Bernoulli $\mu_p$ ($b=2$, $h=1$, $p\in(0,1)\setminus\{\frac12\}$): from the product formula $\hat\mu_p(n)=\prod_{i\ge1}(p+(1-p)e(-n2^{-i}))$,
   $$\gamma(m)=\prod_{i=1}^m\bigl(p+(1-p)e(-2^{-i})\bigr)\prod_{s\ge1}\bigl(p+(1-p)e(2^{-s}-2^{-m-s})\bigr)=\lvert\hat\mu_p(1)\rvert^2+O(2^{-m}).$$
   So $\sigma=\lvert\hat\mu_p(1)\rvert^2\delta_0+f\,d\theta$ with $f$ real-analytic. Since $\int f=1-\lvert\hat\mu_p(1)\rvert^2>0$, $f\not\equiv0$, and so $\log f\in L^1$.
5. By Szegő's theorem (external input, nonconstant density), $\lim_r(\det H_r)^{1/r}=\exp\int\log f>0$, although $a(\mu_p)=0$.

Time-shift determinants therefore detect non-atomic, linearly unpredictable behaviour, not Lebesgue mass. They are a candidate route to $D^+<1$ that does not require $a_*>0$ (§6).

### 1.6 Lean-ready finite statements (uncompiled blueprint for Track H)

The finite lemmas below need no analysis. Statement 10 uses only interval integrals. Mathlib names are indicative: `InnerProductSpace.gramSchmidt` exists, and a Gram-determinant/Gram–Schmidt product lemma may need to be added.

```lean
import Mathlib
open Matrix BigOperators Finset Complex

namespace NormalityChecker.ToeplitzUniformity

/-- normalized Weyl sum of unimodular points -/
noncomputable def weylSum {N : ℕ} (z : Fin N → ℂ) (k : ℤ) : ℂ := (N : ℂ)⁻¹ * ∑ n, z n ^ k

/-- orbit Toeplitz Gram matrix `G j k = S (k - j)` -/
noncomputable def orbitGram {N : ℕ} (z : Fin N → ℂ) (r : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun j k => weylSum z ((k : ℤ) - (j : ℤ))

variable {N r : ℕ} (z : Fin N → ℂ) (hz : ∀ n, ‖z n‖ = 1) (hN : 0 < N)
-- Lean 4 adds `hz`, `hN` to a theorem only if they are mentioned or `include`d;
-- statements 1, 2, 4–6, 8 and 9 need them.

-- 1. quadratic form (finite Fourier identity)
theorem orbitGram_quadForm (a : Fin r → ℂ) :
    star a ⬝ᵥ (orbitGram z r *ᵥ a) = ((N : ℂ)⁻¹) * ∑ n, ((‖∑ j, a j * z n ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) := sorry
-- 2. positive semidefinite, Hermitian, unit diagonal
theorem orbitGram_posSemidef : (orbitGram z r).PosSemidef := sorry
-- 3. Gram–Schmidt product formula for any family in an inner product space.
--    Mathlib's `⟪x, y⟫_ℂ` is conjugate-linear in the FIRST slot, the opposite of §0's
--    ⟨u, v⟩ = ∑ uₙ v̄ₙ.  So the §0 entry ⟨v_k, v_j⟩ is `⟪v j, v k⟫_ℂ`, and for
--    vⱼ = N^{-1/2} (zₙ ^ j)ₙ with ‖zₙ‖ = 1 one has `orbitGram z r j k = ⟪v j, v k⟫_ℂ`:
--    statement 3 applies to `orbitGram` with no transpose.
theorem det_gram_eq_prod_gramSchmidt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : Fin r → E) :
    (Matrix.of fun j k => ⟪v j, v k⟫_ℂ).det = ∏ j, ((‖InnerProductSpace.gramSchmidt ℂ v j‖ ^ 2 : ℝ) : ℂ) := sorry
-- 4. sharp inequality (A1.1), any r ≥ 1, singular case included
theorem orbitGram_det_le (hr : 1 ≤ r) :
    (orbitGram z r).det.re ≤ (1 - ‖weylSum z 1‖ ^ 2) ^ (r - 1) ∧ (orbitGram z r).det.im = 0 := sorry
-- 5. equality characterization
theorem orbitGram_det_eq_iff (hr : 1 ≤ r) :
    (orbitGram z r).det.re = (1 - ‖weylSum z 1‖ ^ 2) ^ (r - 1) ↔
      ∀ k : ℕ, k < r → weylSum z k = weylSum z 1 ^ k := sorry
-- 6. monotone normalized root and Fischer with remainder block
theorem orbitGram_det_pow_antitone {m : ℕ} (hm : m ≤ r) :
    (orbitGram z r).det.re ^ m ≤ (orbitGram z m).det.re ^ r := sorry
theorem orbitGram_det_fischer {m : ℕ} (hm : 0 < m) :
    (orbitGram z r).det.re ≤ (orbitGram z m).det.re ^ (r / m) * (orbitGram z (r % m)).det.re := sorry
-- 7. compound-symmetric determinant (A4), any commutative ring
theorem det_compound {R : Type*} [CommRing R] (α : R) (hr : 1 ≤ r) :
    ((1 - α) • (1 : Matrix (Fin r) (Fin r) R) + α • Matrix.of fun _ _ => (1 : R)).det
      = (1 - α) ^ (r - 1) * (1 + ((r : R) - 1) * α) := sorry
-- 8. Cauchy–Binet / Vandermonde expansion (A7)
theorem orbitGram_det_cauchyBinet :
    (N : ℂ) ^ r * (orbitGram z r).det
      = ∑ s ∈ (univ : Finset (Fin N)).powersetCard r,
          ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ((‖z p.1 - z p.2‖ ^ 2 : ℝ) : ℂ) := sorry
-- 9. 2×2 determinant and the per-N Weyl–discrepancy inequalities (A6.2)
theorem orbitGram_two_det : (orbitGram z 2).det = 1 - ((‖weylSum z 1‖ ^ 2 : ℝ) : ℂ) := sorry
-- 10. exact Koksma constant for a finite point set t : Fin N → ℝ in [0,1)
--     ‖(1/N) ∑ e(h t_n)‖ ≤ 2 |h| D_N(t), with D_N the extreme half-open discrepancy
end NormalityChecker.ToeplitzUniformity
```

Statements 1–9 are finite matrix identities and inequalities. Statement 7 can be proved by the matrix determinant lemma (`Matrix.det_one_add_col_mul_row`) for $\alpha\ne1$, extended as a polynomial identity in $\alpha$. Statement 8 needs Cauchy–Binet for an $r\times N$ times $N\times r$ product.

---

## 2. Track A2: determinant-to-uniformity transfer

**Theorem 2.1 (A2; Paper proof).** Let $h\ne0$, let $1\le r(N)$ with $r(N)\to\infty$, and suppose
$$\liminf_{N\to\infty}\bigl(\det G_{N,r(N)}(h)\bigr)^{1/r(N)}\ge c>0 .$$
Then every $\mu\in C_b(x)$ satisfies $\mu\ge c\lambda$, i.e. $a(\mu)\ge c$. Consequently:

1. $D^+(x;b)\le1-c$.
2. For every word $w$ of length $L$, $\liminf_Nf_w(N;x,b)\ge c\,b^{-L}$ and $\limsup_Nf_w(N;x,b)\le1-c(1-b^{-L})$.
3. If $c=1$, then $C_b(x)=\{\lambda\}$, $D_N\to0$, and $x$ is normal in base $b$.

The hypothesis forces $r(N)\le N$ eventually, because $\det G_{N,r}=0$ for $r>N$ (Proposition 1.6). The proof uses Lemmas 2.2–2.5 and Proposition 2.4.

### 2.1 Invariance and the structure of invariant measures

**Lemma 2.2 (Paper proof).**

1. Every $\mu\in C_b(x)$ is $T_b$-invariant.
2. If $\mu$ is $T_b$-invariant, then $(T_b)_*\mu_{ac}\ll\lambda$ and $(T_b)_*\mu_s\perp\lambda$. Hence $(T_b)_*\mu_{ac}=\mu_{ac}$ and $(T_b)_*\mu_s=\mu_s$.
3. If $\mu$ is $T_b$-invariant, then $\mu_{ac}=a(\mu)\lambda$ with $a(\mu)=\mu_{ac}(\mathbb{T})\in[0,1]$.

*Proof.*

1. $(T_b)_*\mu_N-\mu_N=\frac1N(\delta_{t_N}-\delta_{t_0})$ has total variation at most $2/N$. $T_b$ is continuous **as a circle map**, so $f\circ T_b\in C(\mathbb{T})$ for $f\in C(\mathbb{T})$. Along $\mu_{N_i}\to\mu$, $\int f\circ T_b\,d\mu_{N_i}\to\int f\circ T_b\,d\mu$ and $\int f\,d\mu_{N_i}\to\int f\,d\mu$, and the difference of the left sides is at most $2\lVert f\rVert_\infty/N_i$.
2. *Absolutely continuous part.* If $\lambda(E)=0$ then $\lambda(T_b^{-1}E)=\lambda(E)=0$, because $T_b^{-1}E=\bigcup_{j<b}(E+j)/b$. So $\mu_{ac}(T_b^{-1}E)=0$.
   *Singular part.* $\mu_s$ is concentrated on a Borel set $Z$ with $\lambda(Z)=0$. $T_b(Z)=\bigcup_{j<b}T_b(Z\cap[\frac jb,\frac{j+1}b))$ is a finite union of affine images, each scaled by $b$. So it is Borel with $\lambda(T_b(Z))\le b\lambda(Z)=0$. Since $T_b^{-1}(\mathbb{T}\setminus T_bZ)\subseteq\mathbb{T}\setminus Z$, $(T_b)_*\mu_s$ is concentrated on the null set $T_b(Z)$.
   *Conclusion.* $\mu=(T_b)_*\mu_{ac}+(T_b)_*\mu_s$ is a decomposition into an absolutely continuous and a singular part, and uniqueness of the Lebesgue decomposition gives both invariances.
3. Write $\mu_{ac}=w\,d\lambda$ with $w\in L^1$. Invariance gives $\widehat{\mu_{ac}}(k)=\int e(-kbt)\,d\mu_{ac}=\widehat{\mu_{ac}}(bk)$, hence $\widehat{\mu_{ac}}(k)=\widehat{\mu_{ac}}(b^jk)\to0$ as $j\to\infty$ for every $k\ne0$, by Riemann–Lebesgue. By Fourier uniqueness for finite measures, $\mu_{ac}=\widehat{\mu_{ac}}(0)\lambda$. ∎

*Correction to the proposed justification.* The property "$M^{-1}(E)$ is null whenever $E$ is null" shows only that pushforwards of **absolutely continuous** measures stay absolutely continuous. That **singular** measures stay singular needs the opposite property, that **forward images** of null sets are null (Lusin's property (N)). For $T_b$ and $M_h$ it holds because both maps are finite-to-one and piecewise affine. Both properties are used, in Lemma 2.2 and in Lemma 2.3.

**Lemma 2.3 (pushforward by $M_h$; Paper proof).** Let $\mu$ be $T_b$-invariant, $h\ne0$ and $\nu=(M_h)_*\mu$. Then the Lebesgue decomposition of $\nu$ is
$$\nu=a(\mu)\lambda+(M_h)_*\mu_s .$$
For $h>0$ the density formula reads $w_\nu(\theta)=\frac1h\sum_{j=0}^{h-1}w_\mu\bigl(\frac{\theta+j}{h}\bigr)$. For $h<0$, compose with the reflection $\theta\mapsto-\theta$. With $w_\mu\equiv a(\mu)$ this gives $w_\nu=a(\mu)$ almost everywhere.

*Proof.*

- $(M_h)_*\lambda=\lambda$: $M_{\lvert h\rvert}^{-1}E=\bigcup_{j<\lvert h\rvert}(E+j)/\lvert h\rvert$, and reflection preserves $\lambda$. The density formula is the change of variables $\int f(ht)w(t)\,dt=\int_0^1f(\theta)\frac1h\sum_jw(\frac{\theta+j}h)\,d\theta$.
- $(M_h)_*\mu_s\perp\lambda$: $\mu_s$ lives on a null Borel $Z$. $M_h(Z)$ is a finite union of affine images of pieces of $Z$, scaled by $\lvert h\rvert$, so it is Borel and null, and $(M_h)_*\mu_s$ is concentrated on it, exactly as in Lemma 2.2. Thus $M_h$ never converts singular mass into absolutely continuous mass.
- By uniqueness of the decomposition, $\nu_{ac}=a(\mu)\lambda$. ∎

In particular the asymptotic determinant rate, which is $a(\mu)$ by Proposition 2.4, is **independent of $h$**.

### 2.2 The Szegő step: a self-contained proof of the case needed

**Proposition 2.4 (constant-density Kolmogorov–Krein–Szegő; Paper proof, self-contained).** Let $\rho=a\lambda+\rho_s$ with $a\ge0$ and $\rho_s\perp\lambda$ a finite positive measure. Then:

1. $T_m(\rho)\succeq aI_m$ for every $m$. Hence $D_m(\rho)^{1/m}\ge a$ and $d_m(\rho)\ge a$.
2. $\lim_{m\to\infty}d_m(\rho)=\lim_{m\to\infty}D_m(\rho)^{1/m}=a$.

*Proof.*

*Item 1.* $T_m(\rho)=aT_m(\lambda)+T_m(\rho_s)=aI+T_m(\rho_s)$, and $T_m(\rho_s)\succeq0$ because $a^*T_m(\rho_s)a=\int\lvert q\rvert^2d\rho_s$. The bound $d_m\ge a$ follows from $\int\lvert p\rvert^2d\rho\ge a\int\lvert p\rvert^2d\lambda\ge a$ for monic $p$.

*Item 2, construction.* Fix $\varepsilon\in(0,1)$ and $M>0$.

- *Isolate the singular mass.* Since $\rho_s$ is concentrated on a $\lambda$-null Borel set, inner regularity gives a compact $K$ with $\lambda(K)=0$ and $\rho_s(\mathbb{T}\setminus K)<\varepsilon$. Outer regularity of $\lambda$ gives an open $U\supseteq K$ with $\lambda(U)<\varepsilon/M$.
- *Smooth cutoff.* Choose $\varphi\in C^\infty(\mathbb{T})$ with $0\le\varphi\le1$, $\varphi=1$ on $K$ and $\operatorname{supp}\varphi\subset U$.
- *Analytic extension.* Put $u=-M\varphi$. Its conjugate function $\tilde u$ has Fourier coefficients $-i\,\mathrm{sgn}(k)\hat u(k)$, which decay rapidly, so $\tilde u$ is smooth. $G=u+i\tilde u$ has $\hat G(k)=0$ for $k<0$ and absolutely summable Fourier series, so $G$ extends holomorphically to the disc and continuously to its closure.
- *Outer function.* $F=e^G$ is smooth on $\mathbb{T}$, has Fourier support in $k\ge0$ (Cauchy's theorem), and satisfies $\lvert F\rvert=e^{-M\varphi}$. So $\lvert F\rvert\le1$ everywhere, $\lvert F\rvert=e^{-M}$ on $K$, and $\hat F(0)=F(0)=e^{\hat u(0)}=e^{-M\int\varphi}\ge e^{-\varepsilon}$.
- *Polynomial approximants.* The Fourier partial sums $P_n=\sum_{k=0}^n\hat F(k)z^k$ converge to $F$ uniformly. So $q_n=P_n/\hat F(0)$ are polynomials with constant term $1$, $q_n\to F/F(0)$ uniformly, and
$$\lim_n\int\lvert q_n\rvert^2d\rho=\frac{a\int\lvert F\rvert^2d\lambda+\int\lvert F\rvert^2d\rho_s}{\lvert F(0)\rvert^2}\le e^{2\varepsilon}\bigl(a+e^{-2M}\rho_s(\mathbb{T})+\varepsilon\bigr).$$

*Item 2, conclusion.* For $m\ge\deg q_n$, the reversed polynomial $p(z)=z^m\overline{q_n(1/\bar z)}$ is monic of degree $m$ with $\lvert p\rvert=\lvert q_n\rvert$ on $\mathbb{T}$. Hence $d_m(\rho)\le\int\lvert q_n\rvert^2d\rho$ for all large $m$. Since $\varepsilon$ and $M$ are arbitrary, $\limsup_md_m(\rho)\le a$, and item 1 gives $\lim d_m=a$. Finally $D_m=\prod_{j<m}d_j$ (Lemma 1.1, with $d_j(\rho)$ defined in $L^2(\rho)$). So $\frac1m\log D_m$ is a Cesàro mean of $\log d_j\to\log a$ (or $\to-\infty$ when $a=0$), and $D_m^{1/m}\to a$. ∎

**Theorem S (Szegő–Kolmogorov–Krein; External input, cited and not needed for A2, A3 or A6).** Let $\rho$ be any finite positive Borel measure on $\mathbb{T}$ with $d\rho=w\,d\lambda+d\rho_s$. Then
$$\lim_{m\to\infty}D_m(\rho)^{1/m}=\exp\int\log w\,d\lambda ,$$
with the right side read as $0$ when $\int\log w=-\infty$. No regularity of $w$ is assumed. When $\rho$ has finite support, $D_m=0$ for $m>\#\operatorname{supp}\rho$, and both sides vanish.

- Szegő (1915, 1920) proved the case of absolutely continuous measures.
- Kolmogorov (1941) and Krein (1945) showed that the singular part does not contribute.
- References: U. Grenander and G. Szegő, *Toeplitz Forms and Their Applications* (1958), Ch. 3; B. Simon, *Orthogonal Polynomials on the Unit Circle, Part 1* (AMS Colloq. Publ. 54.1, 2005), Ch. 2. The theorem numbers 2.3.1 and 2.7.14 quoted in the coordinator brief were not independently re-checked against the printed edition here, so we cite the chapter.
- Equivalent Verblunsky form: $\prod_k(1-\lvert\alpha_k\rvert^2)=\exp\int\log w$.

Proposition 2.4 is the special case $w\equiv a$. Its proof above makes Theorems 2.1, 3.1 and 6.1 independent of the general theorem. Theorem S is used only in Proposition 1.8(5).

### 2.3 Proof of Theorem 2.1

Fix $\mu\in C_b(x)$ with $\mu_{N_i}\to\mu$, and put $\nu=(M_h)_*\mu$.

1. Fix $m\ge1$. For all $N$ with $r(N)\ge m$, Corollary 1.5(2) gives $(\det G_{N,r(N)})^{1/r(N)}\le(\det G_{N,m})^{1/m}$.
2. $G_{N_i,m}(h)_{jk}=\int e((k-j)ht)\,d\mu_{N_i}\to\int e((k-j)ht)\,d\mu=T_m(\nu)_{jk}$, because the integrand is continuous. The determinant is continuous.
3. Steps 1 and 2 give $c\le\liminf_i(\det G_{N_i,r(N_i)})^{1/r(N_i)}\le(\det T_m(\nu))^{1/m}$ for every $m$.
4. By Lemma 2.2, $\mu$ is invariant. By Lemma 2.3, $\nu=a(\mu)\lambda+\nu_s$ with $\nu_s\perp\lambda$. Letting $m\to\infty$ in step 3 and applying Proposition 2.4 to $\rho=\nu$ gives $c\le a(\mu)$.
5. So $\mu\ge\mu_{ac}=a(\mu)\lambda\ge c\lambda$. The consequences follow from Lemma 2.5. ∎

*Variant with Hadamard–Fischer, as proposed in the brief.* Corollary 1.5(3) gives $(\det G_{N,r})^{1/r}\le(\det G_{N,m})^{\lfloor r/m\rfloor/r}$, where the remainder factor is at most $1$ by Hadamard. Here $\lfloor r/m\rfloor/r\to1/m$ and $\lfloor r/m\rfloor/r\ge1/(2m)$ for $r\ge m$. If $\det T_m(\nu)>0$, continuity of $y\mapsto y^{e}$ on $(0,1]$ gives the same bound as step 3. If $\det T_m(\nu)=0$, the right side is at most $(\det G_{N_i,m})^{1/(2m)}\to0$, contradicting $c>0$. So the brief's route is also correct, with this case distinction.

### 2.4 From domination to discrepancy and word frequencies, with atoms

**Lemma 2.5 (Paper proof).** Suppose every $\mu\in C_b(x)$ satisfies $\mu\ge c\lambda$.

1. For every open arc $U$, $\liminf_N\mu_N(U)\ge c\lambda(U)$.
2. For every $\varepsilon>0$ there is $N_0$ such that $\mu_N(J)\ge c\lambda(J)-\varepsilon$ for **all** half-open circular arcs $J$ and all $N\ge N_0$.
3. $D^+\le1-c$.
4. $\liminf f_w\ge c\,b^{-L}$ and $\limsup f_w\le1-c(1-b^{-L})$.
5. If $c=1$, then $D_N\to0$.

*Proof.*

1. Take a subsequence realizing $\liminf\mu_N(U)$ and refine it so that $\mu_{N_i}\to\mu\in C_b(x)$. The Portmanteau theorem for **open** sets gives $\liminf\mu_{N_i}(U)\ge\mu(U)\ge c\lambda(U)$.
2. Fix $K$ with $2c/K\le\varepsilon/2$, and let $\mathcal A$ be the finite family of open arcs with endpoints in $\frac1K\mathbb{Z}$. By item 1 there is $N_0$ with $\mu_N(A)\ge c\lambda(A)-\varepsilon/2$ for all $A\in\mathcal A$ and $N\ge N_0$. A half-open arc $J$ of length $\ell$ contains the open arc $A$ between the first grid point at or after its left end and the last grid point at or before its right end, and $\lambda(A)\ge\ell-2/K$. If $\ell<2/K$ the claim is trivial. So $\mu_N(J)\ge\mu_N(A)\ge c(\ell-2/K)-\varepsilon/2\ge c\ell-\varepsilon$.
3. For $J=[u,v)\subset[0,1)$, item 2 gives $\lambda(J)-\mu_N(J)\le(1-c)\lambda(J)+\varepsilon\le1-c+\varepsilon$. Also $\mu_N(J)-\lambda(J)=\lambda(J^c)-\mu_N(J^c)\le(1-c)\lambda(J^c)+\varepsilon$, where $J^c$ is a half-open circular arc.
4. $f_w(N)=\mu_N(I_w)\ge\mu_N(\operatorname{int}I_w)$ and $\lambda(\operatorname{int}I_w)=b^{-L}$. For the upper bound, $I_w^c$ is a finite union of arcs whose interiors have total length $1-b^{-L}$.
5. Item 3 with $c=1$ gives $D^+\le0$, which is the repository's definition of normality. ∎

**Why the open-interior argument is necessary.** Weak convergence does not control the masses of half-open cylinders that carry atoms on their boundary. Take the explicit law $\mu_\alpha=\alpha\delta_0+(1-\alpha)\lambda$ of §4. Orbit points that approach $0$ **from the right** contribute to the cylinder $0^L$, and points approaching **from the left** contribute to $(b-1)^L$. Both behaviours have the same weak limit, so $\lim f_{0^L}$ is not determined by $\mu_\alpha$ (Proposition 4.3 in §4.2 realizes the first behaviour). The lower bound $c\,b^{-L}$ uses only interiors, so atoms at $b$-adic endpoints cannot break it.

### 2.5 Fixed points, $D^+=1$ and $K_b$

**Lemma 2.6 (Paper proof).** The fixed points of $T_b$ on $\mathbb{T}$ are $\tau_j=j/(b-1)$, $0\le j\le b-2$.

1. $D^+(x;b)=1$ iff $\delta_{\tau_j}\in C_b(x)$ for some $j$.
2. $x\in K_b$ iff $C_b(x)=\{\delta_{\tau_j}\}$ for a single $j$.

*Proof.*

1. ($\Rightarrow$) Suppose $D_{N_i}\to1$. Then there are half-open arcs $A_i$ with $\lambda(A_i)\to0$ and $\mu_{N_i}(A_i)\to1$: either $J_i$ itself, or its complement when $\lambda(J_i)\to1$ and $\mu_{N_i}(J_i)\to0$. Refine so that the left endpoints of $A_i$ converge to $\tau$ and $\mu_{N_i}\to\mu$. For each $\varepsilon>0$, $A_i$ eventually lies in the closed arc $[\tau-\varepsilon,\tau+\varepsilon]$, so Portmanteau for closed sets gives $\mu([\tau-\varepsilon,\tau+\varepsilon])=1$. Hence $\mu=\delta_\tau$, and invariance gives $b\tau\equiv\tau$, i.e. $\tau=\tau_j$.
   ($\Leftarrow$) If $\mu_{N_i}\to\delta_{\tau_j}$, then $\mu_{N_i}((\tau_j-\varepsilon,\tau_j+\varepsilon))\to1$, so $D_{N_i}\ge1-3\varepsilon$ eventually, using Lemma 0.1(2).
2. Since $\lVert\mu_{N+1}-\mu_N\rVert_{TV}\le2/(N+1)\to0$, $C_b(x)$ is connected. If $D_N\to1$, every limit is a fixed-point Dirac by item 1, and connectedness leaves a single one. The converse is item 1 applied along the full sequence. ∎

For $b\ge3$ there are $b-1\ge2$ fixed points. For example, $\tau=1/2$ is fixed in base 3, corresponding to the digit sequence $1111\ldots$.

### 2.6 What the determinant programme measures: mass on normal numbers

**Proposition 2.7 (A2.6; Paper proof).** For every $T_b$-invariant probability measure $\mu$, $a(\mu)=\mu(\mathcal N_b)$. Hence $a_*=\inf_{\mu\in C_b(x)}\mu(\mathcal N_b)$.

*Proof.* $\mathcal N_b$ is Borel, $T_b^{-1}\mathcal N_b=\mathcal N_b$ (normality is shift-invariant), and $\lambda(\mathcal N_b)=1$ by Borel's theorem.

- The restriction $\mu'=\mu|_{\mathcal N_b}$ is invariant: $\mu'(T_b^{-1}E)=\mu(T_b^{-1}(E\cap\mathcal N_b))=\mu'(E)$.
- For $f\in C(\mathbb{T})$ and $A_Nf=\frac1N\sum_{n<N}f\circ T_b^n$, invariance gives $\int f\,d\mu'=\int A_Nf\,d\mu'$. On $\mathcal N_b$, $A_Nf\to\int f\,d\lambda$ pointwise, which is the definition of normality, and $\lvert A_Nf\rvert\le\lVert f\rVert_\infty$. Bounded convergence gives $\int f\,d\mu'=\mu(\mathcal N_b)\int f\,d\lambda$, so $\mu'=\mu(\mathcal N_b)\lambda$.
- $\mu|_{\mathbb{T}\setminus\mathcal N_b}$ is singular, since $\lambda(\mathbb{T}\setminus\mathcal N_b)=0$.
- By uniqueness of the Lebesgue decomposition, $\mu_{ac}=\mu(\mathcal N_b)\lambda$. ∎

No ergodic decomposition or Birkhoff theorem is needed. Every ergodic invariant $\mu\ne\lambda$ (Bernoulli, Markov, periodic) has $a(\mu)=0$.

---

## 3. Track A3: the optimal growing-dimension rate

### 3.1 The optimal rate $a_*$

**Theorem 3.1 (A3; Paper proof).** For every $x$, $b\ge2$ and $h\ne0$,
$$\sup_{\substack{r(N)\to\infty\\ 1\le r(N)\le N}}\ \liminf_{N\to\infty}\bigl(\det G_{N,r(N)}(h)\bigr)^{1/r(N)}=a_*:=\inf_{\mu\in C_b(x)}a(\mu)=\inf_{\mu\in C_b(x)}\mu(\mathcal N_b).$$
Moreover:

1. The supremum is attained.
2. If $r_{\rm opt}$ attains it, so does every $r'(N)\to\infty$ with $r'\le r_{\rm opt}$.
3. For each fixed $m$, $\liminf_N\lambda_{\min}(G_{N,m}(h))=\min_{\mu\in C_b(x)}\lambda_{\min}(T_m((M_h)_*\mu))\ge a_*$.
4. The value does not depend on $h$.

*Proof.*

- *Upper bound ($\le$).* If the $\liminf$ along $r(N)$ is $c>0$, Theorem 2.1 gives $a(\mu)\ge c$ for all $\mu\in C_b(x)$, so $c\le a_*$. If $c=0$ there is nothing to prove.
- *Fixed dimension (item 3).* $\lambda_{\min}$ is continuous and $C_b(x)$ is compact and equals the set of limit points of $(\mu_N)$. So $\liminf_N\lambda_{\min}(G_{N,m})=\min_{\mu\in C_b(x)}\lambda_{\min}(T_m(\nu_\mu))$. By Lemma 2.3 and Proposition 2.4(1), $T_m(\nu_\mu)\succeq a(\mu)I\succeq a_*I$.
- *Diagonal selection ($\ge$, item 1).* By item 3, for each $m$ there is $N_m$ with $\lambda_{\min}(G_{N,m})\ge a_*-1/m$ for all $N\ge N_m$. Take $N_1=1$, make $N_m$ nondecreasing, and put $r(N)=\max\{m\le N:N_m\le N\}$. Then $r(N)\le N$, $r(N)\to\infty$, and $(\det G_{N,r(N)})^{1/r(N)}\ge\lambda_{\min}(G_{N,r(N)})\ge a_*-1/r(N)$, since all eigenvalues are at least $\lambda_{\min}\ge0$.
- *Item 2.* Corollary 1.5(2): if $r'\le r$, then $(\det G_{N,r'})^{1/r'}\ge(\det G_{N,r})^{1/r}$.
- *Item 4.* Lemma 2.3. ∎

The theorem identifies exactly what the determinant programme measures: the **smallest guaranteed Lebesgue component**, equivalently the smallest mass on normal numbers, over all limiting orbit distributions. It is **not** equivalent to $D^+<1$ (§3.2).

### 3.2 Strict separation from $D^+<1$

**Proposition 3.2 ($a_*>0$ is strictly stronger than $D^+<1$; Paper proof, Finite certificate).**

1. $a_*>0$ implies $D^+\le1-a_*$ and $\liminf f_w\ge a_*b^{-L}$ for every word (Lemma 2.5).
2. Let $p\in(0,1)\setminus\{\frac12\}$ and let $\mu_p$ be the Bernoulli measure in base 2 with $\Pr(\text{digit }0)=p$, and $q=\min(p,1-p)$. For $\mu_p$-almost every $x$:
   - $C_2(x)=\{\mu_p\}$, by Birkhoff's theorem for the ergodic $\mu_p$ applied to a countable dense subset of $C(\mathbb{T})$ (external, standard).
   - $a_*=0$: by the strong law, $\mu_p(\mathcal N_2)=0$, and Proposition 2.7 applies.
   - $\lim_N(\det G_{N,r(N)}(h))^{1/r(N)}=0$ for **every** $r(N)\to\infty$, since the root is at most $(\det G_{N,m})^{1/m}\to D_m(\nu)^{1/m}$ for each fixed $m$, and $\inf_mD_m(\nu)^{1/m}=0$.
   - Every word $w$ has limiting frequency $p^{\#0(w)}(1-p)^{\#1(w)}>0$, because $\mu_p$ is atomless, so $\mu_p(\partial I_w)=0$.
   - $D_N\to D(\mu_p)$, by Pólya's uniform convergence of distribution functions to a continuous limit, and
   $$D(\mu_p)\le\max\bigl(2(1-q)^k,\ 1-q^k,\ 2^{1-k}\bigr)<1,\qquad k=\min\{k:2(1-q)^k<1\}.$$

For $p=\frac13$ the bound is $8/9$. The script's exact dyadic computation at level $12$ gives the enclosure
$$D(\mu_{1/3})\in[0.239065,\ 0.247017],$$
outward-rounded and asserted as exact `Fraction` comparisons: $D_{\rm grid}=\frac{520393063}{2176782336}\ge0.239065$ and $D_{\rm up}=\frac{67212715}{272097792}\le0.247017$.

*Proof of the explicit bound.* Every level-$k$ dyadic interval has $\mu_p$-mass in $[q^k,(1-q)^k]$.

- An interval with $\lambda(J)\le2^{-k}$ is covered by two level-$k$ intervals, so $\mu_p(J)-\lambda(J)\le2(1-q)^k$.
- Otherwise $\mu_p(J)-\lambda(J)\le1-2^{-k}\le1-q^k$.
- An interval with $\lambda(J)\ge2^{1-k}$ contains a level-$k$ interval, so $\lambda(J)-\mu_p(J)\le1-q^k$.
- Otherwise $\lambda(J)-\mu_p(J)<2^{1-k}$.

*Enclosure.* On each cell, $R=F_p-t$ varies within $[-2^{-K},\max\text{cell mass}]$, where $F_p$ is the distribution function of $\mu_p$. ∎

So biased Bernoulli points satisfy $D^+<1$ and have every word at positive frequency, yet carry no Lebesgue component: every determinant schedule decays to $0$. **Positive word frequencies do not imply a positive Lebesgue component.**

### 3.3 Quantitative and effective diagonal selection

- *Explicit selection from explicit rates.* Suppose explicit functions $\varepsilon_m(N)\to0$ are known with $\lambda_{\min}(G_{N,m})\ge a_*-\varepsilon_m(N)$. Take $\varepsilon_1\equiv0$, which is valid because $G_{N,1}=(1)$ and $a_*\le1$. Then $r(N)=\max\{m\le N:\varepsilon_j(N)\le1/j\ \forall j\le m\}$ is well defined, since $m=1$ always qualifies. It is computable from the $\varepsilon_j$, tends to $\infty$, and is optimal, because $(\det G_{N,r(N)})^{1/r(N)}\ge\lambda_{\min}(G_{N,r(N)})\ge a_*-1/r(N)$.
- *Normal $x$ with $D_N\le\varepsilon(N)$.* Theorem 5.2 gives $\lambda_{\min}(G_{N,m}(h))\ge1-\pi\lvert h\rvert(m-1)\varepsilon(N)$. So $r(N)=1+\lfloor\eta/(\pi\lvert h\rvert\varepsilon(N))\rfloor$ is an explicit schedule with root at least $\exp(-\eta^2/(2(1-\eta)))$ (§5.3).
- *Existence without effectivity.* In general, though, the existence of an optimal slowly growing $r(N)$ does not supply a usable rate. Propositions 3.4–3.6 (§3.4) make this precise.

### 3.4 Non-effectivity and the absence of universal schedules

**Proposition 3.4 (non-effectivity; Paper proof, External input).**

1. No finite prefix of digits determines $a_*$. Every prefix extends to a normal number ($a_*=1$) and to a member of $K_b$ ($a_*=0$), because a finite edit does not change $C_b(x)$.
2. $a_*(x)=1$ iff $x$ is normal: Theorem 2.1 with $c=1$, and conversely $C_b(x)=\{\lambda\}$. Hence $\{x\in\mathbb{R}:a_*(x)=1\}=\mathcal N_b+\mathbb{Z}$ is $\Pi^0_3$-complete in the Borel hierarchy (Ki–Linton 1994).
3. *(External input `AC-11`.)* On digit-oracle program codes, recognizing $a_*=1$, which by item 2 means recognizing normality, is neither computable, nor c.e., nor co-c.e. `AC-11` kernel-verifies this for $b=2$, taking the endpoint properties of the two switched digit oracles as explicit inputs. Its halting-switch construction transfers verbatim to every $b\ge2$, with a computable base-$b$ normal oracle (Champernowne) and a computable member of $K_b$ ($L_b$) as endpoints. That transfer is a paper deduction and is not kernel-verified.

Item 3 does **not** by itself exclude a uniform algorithm for optimal schedules. Suppose an algorithm produced, uniformly in a program $e$, an optimal computable schedule $r_e$. Then $a_*(x_e)=1$ would be equivalent to $\liminf_N(\det G_{N,r_e(N)}(1))^{1/r_e(N)}=1$, that is, to $\forall\varepsilon\,\exists M\,\forall N\ge M:\ (\det G_{N,r_e(N)}(1))^{1/r_e(N)}\ge1-\varepsilon$. The root is a computable real uniformly in $(e,N)$, so the inner inequality is $\Pi^0_1$ and the whole condition is still $\Pi^0_3$. No contradiction with item 3 arises. The non-existence of such an algorithm is proved separately, by diagonalization, in Proposition 3.6.

**Proposition 3.5 (no universal schedule, even for normal numbers; Paper proof).** Let $r(N)\to\infty$ be **any** schedule. Then there is a normal $x$, computable if $r$ is, with
$$\liminf_{N}\bigl(\det G_{N,r(N)}(1)\bigr)^{1/r(N)}=0 .$$

*Proof.* Let $m_k=k$ and $P_k=b^{k}$, and let $\beta_k$ be a de Bruijn cycle of order $k$ over the $b$ digits. Stage $k$ appends $\beta_k$ repeated $R_k$ times. Write $N_k$ for the total length after stage $k$. Choose $R_k$ so large that $r(N_k)\ge2P_k$ and $N_k\ge16^{P_k}(N_{k-1}+s_k)$, where $s_k=2P_k$.

*Small determinants.* The $P_k$ rotations of $\beta_k^\infty$ give $P_k$ distinct periodic points $y^{(i)}$. A position with at least $s_k$ digits left in stage $k$ lies within $b^{-s_k}$ of one of them.

- For $j\ge P_k$ let $p(z)=z^{j-P_k}\prod_i(z-e(y^{(i)}))$. It is monic of degree $j$, with $\lvert p\rvert\le2^{P_k}$ on $\mathbb{T}$ and $\lvert p(e(t))\rvert\le2^{P_k}\cdot2\pi\,\operatorname{dist}(t,\{y^{(i)}\})$.
- Hence $d_j(\mu_{N_k})\le4^{P_k}\bigl(4\pi^2b^{-2s_k}+(N_{k-1}+s_k)/N_k\bigr)\le(4\pi^2+1)\,4^{-P_k}$.
- Since $d_j\le1$ for every $j$ and $r(N_k)\ge2P_k$,
$$(\det G_{N_k,r(N_k)})^{1/r(N_k)}\le\bigl((4\pi^2+1)4^{-P_k}\bigr)^{(r-P_k)/r}\le\bigl((4\pi^2+1)4^{-P_k}\bigr)^{1/2}\to0 .$$

*Normality.* Fix a word $w$ of length $L$. For every stage $j\ge L$, each full period of the cyclic word $\beta_j$ contains exactly $P_jb^{-L}$ occurrences of $w$. Stages $j<L$ have a total length depending only on $L$. So every $N$ with $N_{k-1}<N\le N_k$ satisfies
$$\#\{\text{occurrences of }w\}=Nb^{-L}+O_L(1)+O\Bigl(\sum_{j<k}P_j+kL+\min(P_k,N-N_{k-1})\Bigr).$$
Since $N_{k-1}\ge16^{P_{k-1}}\gg P_k$, the error is $o(N)$. ∎

The optimal schedule therefore genuinely depends on $x$. For normal numbers it is governed by the discrepancy rate (Theorem 5.2), and no rate-free choice works for all of them. The next proposition shows that the dependence cannot be computed uniformly from a program for $x$.

**Proposition 3.6 (no uniformly computable optimal schedule; Paper proof).** Fix an acceptable numbering $(\varphi_e)$ of the partial computable functions $\mathbb{N}\to\mathbb{N}$. Call $e$ a *digit-oracle program* if $\varphi_e$ is total with values in $\{0,\dots,b-1\}$, and put $x_e=\sum_{n\ge0}\varphi_e(n)\,b^{-n-1}$. Let $A(e,N)$ be any partial computable function, read as a candidate schedule $r_e(N)=A(e,N)$. Then there is a digit-oracle program $e^*$ such that one of the following holds:

1. $A(e^*,\cdot)$ is not total, or it is total but does not tend to $\infty$;
2. $A(e^*,\cdot)$ is total and tends to $\infty$, $x_{e^*}$ is normal in base $b$ (so $a_*(x_{e^*})=1$), and
$$\liminf_{N\to\infty}\bigl(\det G_{N,A(e^*,N)}(1)\bigr)^{1/A(e^*,N)}=0 .$$

Consequently no algorithm maps every digit-oracle program $e$ to an optimal schedule $r_e(N)\to\infty$ for $x_e$. More strongly, an algorithm that maps every digit-oracle program to a total schedule tending to $\infty$ fails to be optimal on some program of a normal number.

*Proof.* We diagonalize the construction of Proposition 3.5 against $A$, using Kleene's recursion theorem. Keep $P_k=b^k$, $s_k=2P_k$ and a de Bruijn cycle $\beta_k$ of order $k$, computable uniformly in $k$.

- *A total generator.* For each $e$ define digits $p(e,0),p(e,1),\dots$ in stages, starting from $N_0=0$. Stage $k$ starts at length $N_{k-1}$ and sets $T_k=16^{P_k}(N_{k-1}+s_k)$. At its $t$-th step it emits the next digit of $\beta_k\beta_k\beta_k\cdots$ and runs $t$ steps of each computation $A(e,M)$ with $T_k\le M\le T_k+t$. At the first step at which some such $M$ has halted with $A(e,M)\ge2P_k$, let $M_k$ be the least such $M$. Continue $\beta_k^\infty$ up to the length $N_k=\max(L,M_k)$, where $L$ is the current length, and begin stage $k+1$. Every step emits a digit, so $p(e,n)$ is computed in finitely many steps for every $(e,n)$. This holds even if some stage never ends: the sequence then continues $\beta_k^\infty$ forever. Thus $p$ is total computable with values in $\{0,\dots,b-1\}$.
- *Fixed point.* By the s-m-n theorem there is a total computable $g$ with $\varphi_{g(e)}=p(e,\cdot)$. By Kleene's recursion theorem there is $e^*$ with $\varphi_{e^*}=\varphi_{g(e^*)}=p(e^*,\cdot)$. So $e^*$ is a digit-oracle program, and $x_{e^*}$ is the output of the construction run against its own candidate schedule $A(e^*,\cdot)$.
- *Suppose item 1 fails.* Then $A(e^*,M)\ge2P_k$ for all large $M$, so every stage ends and every $N_k$ is finite.
  - *Normality.* $N_k\ge M_k\ge T_k\ge16^{P_k}$. This is all that the normality argument of Proposition 3.5 uses, and the incomplete final cycle of each stage contributes $O(P_k)$, which is already in its error term. So $x_{e^*}$ is normal, and $a_*(x_{e^*})=1$ by Proposition 3.4(2).
  - *Small determinants.* $N_{k-1}<T_k\le M_k\le N_k$, so the prefix of length $M_k$ ends inside stage $k$. Among its positions, only the $N_{k-1}$ earlier ones and at most $s_k$ positions within distance $s_k$ of the end of stage $k$ lack $s_k$ digits of $\beta_k^\infty$ to their right. The estimate of Proposition 3.5 therefore holds at $N=M_k$: for $j\ge P_k$,
$$d_j(\mu_{M_k})\le4^{P_k}\Bigl(4\pi^2b^{-2s_k}+\frac{N_{k-1}+s_k}{M_k}\Bigr)\le(4\pi^2+1)\,4^{-P_k},$$
    because $M_k\ge T_k$. Put $r=A(e^*,M_k)\ge2P_k$. If $r>M_k$ the determinant is $0$. Otherwise, since $(4\pi^2+1)4^{-P_k}<1$ once $P_k\ge3$,
$$\bigl(\det G_{M_k,r}(1)\bigr)^{1/r}\le\bigl((4\pi^2+1)\,4^{-P_k}\bigr)^{1/2}\to0\qquad(k\to\infty,\ M_k\to\infty).$$
  So item 2 holds. ∎

The generator never computes a determinant; it only watches $A$. Proposition 3.6 is the uniform version of the remark in Proposition 3.5 that its witness is computable when $r$ is.

---

## 4. Track A4: exact controls

### 4.1 Compound-symmetric determinants

**Proposition 4.1 (A4; Paper proof, Finite certificate).** Over any commutative ring and for every $r\ge1$,
$$\det\bigl((1-\alpha)I_r+\alpha J_r\bigr)=(1-\alpha)^{r-1}\bigl(1+(r-1)\alpha\bigr).$$
For real $\alpha$, the eigenvalues are $1+(r-1)\alpha$ (eigenvector $\mathbf 1$) and $1-\alpha$ with multiplicity $r-1$ (eigenvectors $e_0-e_k$). For $\alpha\in[0,1]$,
$$(1-\alpha)^r\le\det\le r(1-\alpha)^{r-1},$$
so $\lim_r(\det)^{1/r}=1-\alpha$. For $\alpha=1$ the determinant is $0$ for $r\ge2$.

*Proof.* $J_r=\mathbf 1\mathbf 1^{T}$ has rank one, so the eigen-decomposition above is complete. For a general ring, both sides are polynomials in $\alpha$ that agree over $\mathbb{Q}$, and hence identically. ∎

The script checks the identity exactly for ten values of $\alpha$, including $\alpha<0$ and $\alpha>1$, and $r\le12$, together with the eigenvectors, the root sandwich and the regularized version. For $\mu_\alpha=\alpha\delta_0+(1-\alpha)\lambda$ we have $(M_h)_*\mu_\alpha=\mu_\alpha$ (because $M_h(0)=0$), $\widehat{\mu_\alpha}(k)=\alpha+(1-\alpha)[k=0]$, and $T_r(\mu_\alpha)=(1-\alpha)I_r+\alpha J_r$. This agrees with Theorem S: $\exp\int\log(1-\alpha)=1-\alpha=a(\mu_\alpha)$.

### 4.2 Sharpness of A2 and explicit witnesses

**Theorem 4.2 (sharpness of A2 across $[0,1]$; Paper proof).** Let $\alpha\in[0,1]$, put $c=1-\alpha$, and suppose $\mu_N\to\mu_\alpha$ along **all** $N$. Then:

1. $a_*=1-\alpha$, and the optimal determinant rate is $1-\alpha$.
2. $D_N\to\alpha=1-c$, so the bound $D^+\le1-c$ is attained.
3. Suppose in addition that $\lim_{\varepsilon\to0^+}\limsup_N\mu_N((1-\varepsilon,1))=0$, i.e. asymptotically no orbit mass approaches the atom at $0$ from the left. Then $f_{(b-1)^L}\to c\,b^{-L}$ for every $L$, so the word bound of Theorem 2.1(2) is attained.

*Proof.* Item 1 is Theorem 3.1. For item 2, the upper bound $D^+\le\alpha$ is Lemma 2.5. For the lower bound, $D_N\ge\mu_N((-\delta,\delta))-2\delta$, and Portmanteau gives $\liminf\ge\alpha+2(1-\alpha)\delta-2\delta$, which tends to $\alpha$ as $\delta\to0$. For item 3, the open arc $(1-b^{-L},1)$ avoids $0$, so Portmanteau gives $\liminf_Nf_{(b-1)^L}(N)\ge\mu_\alpha((1-b^{-L},1))=c\,b^{-L}$. For $0<\varepsilon<b^{-L}$, $f_{(b-1)^L}(N)\le\mu_N([1-b^{-L},1-\varepsilon])+\mu_N((1-\varepsilon,1))$. The closed arc also avoids $0$, so $\limsup_N\mu_N([1-b^{-L},1-\varepsilon])\le c(b^{-L}-\varepsilon)$. Letting $\varepsilon\to0^+$ and using the hypothesis gives $\limsup_Nf_{(b-1)^L}\le c\,b^{-L}$. ∎

**Proposition 4.3 (unconditional witnesses for every $\alpha$; Paper proof).** Let $C=c_1c_2\ldots$ be the base-$b$ Champernowne digit sequence (normal in base $b$; external, classical). For $0<\alpha<1$, let $y_\alpha$ have the digits
$$C\text{-block}_1\,0^{z_1}\,C\text{-block}_2\,0^{z_2}\cdots,$$
where the $k$-th $C$-block consists of the next $k$ digits of $C$ and $z_k=\lfloor k\alpha/(1-\alpha)\rfloor$. Then $\mu_N\to\mu_\alpha$ along all $N$, and $y_\alpha$ is computable when $\alpha$ is.

*Proof.* The concatenated $C$-blocks form exactly a prefix of $C$. So a word $w$ of length $L$ occurs at $C$-positions with frequency $b^{-L}+o(1)$, up to $O(L)$ boundary positions per block. There are $O(\sqrt N)$ blocks up to $N$, and block lengths are $O(\sqrt N)$, so all prefixes $N$ are covered.

Positions inside a zero run, at least $L$ before its end, lie in $[0,b^{-L})$, which is the cylinder $0^L$. Zero-run positions have density $\alpha+o(1)$. Hence every cylinder mass converges to $\mu_\alpha(I_w)$, with the atom placed in $0^L$, which implies weak convergence. The endpoints are $\alpha=0$ (take $C$) and $\alpha=1$ (any member of $K_b$).

These witnesses also satisfy the hypothesis of Theorem 4.2(3). Zero-run positions have first digit $0$, so $t_n<b^{-1}$. A $C$-block position has $t_n\in(1-b^{-s},1)$ only if its next $s$ digits are all $b-1$, which happens with density $(1-\alpha)b^{-s}+o(1)$. Hence $\limsup_N\mu_N((1-b^{-s},1))\le(1-\alpha)b^{-s}\to0$. ∎

**Arithmetic witnesses (External input `GF-45`).** `GF-45` asserts that for each radix $b$ and each $\alpha\in[0,1]$ there is an explicit $x\in K_b$ whose reciprocal $1/x$ has $\mu_N\to\mu_\alpha$ along all prefixes in that radix. This is one witness per pair $(b,\alpha)$, not one witness for all radices, per the Phase 26 Stage 0 correction. `GF-45` is registered with evidence label `Paper proof`. Phase 26 Audit III ([`reviews/audit-3-gf45.md`](reviews/audit-3-gf45.md)) validated it with 0 Critical and 0 Major findings; that audit is a cross-model review, not independent human peer review. Theorem 4.2(1)–(2) therefore apply verbatim, and the reciprocal family realizes the full sharpness range arithmetically. Within Track A this application rests on `GF-45` as an external input and is not reproved here. Proposition 4.3 makes the sharpness statement itself self-contained.

### 4.3 Control table

| Family | Limit measures | $a_*$ | Determinant behaviour | Notes |
| --- | --- | --- | --- | --- |
| Normal numbers: Stoneham $\alpha(b,c)$ (`ST-28`), localized logarithms (`LS-01`), Champernowne | $\{\lambda\}$ | $1$ | Root $\to1$ for every $r(N)=o(1/D_N)$ (Theorem 5.2) | Not uniform over normal numbers (Proposition 3.5) |
| $\mu_\alpha$ witnesses (Proposition 4.3; `GF-45` reciprocals as external input, Audit III passed) | $\{\mu_\alpha\}$ | $1-\alpha$ | Root $\to1-\alpha$ on optimal schedules | Sharpness of A2 for every $c$ |
| Euler product $E_b$ (`GF-03`), Euler cube $E_b^3$ (`GF-04`) | $\{\delta_0\}$ ($K_b$) | $0$ | $\lvert S_N(1)\rvert\to1$; $\det G_{N,r}\to0$ for every $r\ge2$ | Lemma 2.6 |
| $E_2/3$ (`GF-04`, $D_N\to\frac12$) | Carried by $\{0,\frac13,\frac23\}$ | $0$ | $\liminf\det G_{N,2}(1)>0$ but $\det G_{N,4}(1)\to0$ | $D^+=\frac12<1$ with no Lebesgue mass |
| Rational $x$, preperiod $\pi$, period $P$ | Periodic-orbit measure | $0$ | $\det G_{N,r}=0$ exactly for $r>\pi+P$ (Proposition 1.6) | Exact in $\mathbb{Z}[\zeta_Q]$ |
| Primitive-root rationals $a/Q$, full periods | Uniform on $(\mathbb{Z}/Q)^\times/Q$ | $0$ | $G=(1+\beta)I-\beta J$, $\beta=\frac1{Q-1}$, $r\le Q$; $\det=(\frac Q{Q-1})^{r-1}\frac{Q-r}{Q-1}>0$ up to $r=Q-1$, and $0$ at $r=Q$ | Complete cancellation: fixed-$r$ positivity is not a Lebesgue component |
| Biased Bernoulli $p\ne\frac12$ | $\{\mu_p\}$ singular | $0$ | Root $\to0$ for every schedule | All words positive and $D^+<1$ (Proposition 3.2) |
| Stationary Markov measure $\ne\lambda$ (irreducible, aperiodic) | $\{\mu_{\rm M}\}$ singular | $0$ | Root $\to0$ | Mixtures $(1-\beta)\lambda+\beta\mu_{\rm M}$ give $a=1-\beta$ |
| Maximally nonnormal $L_b=\sum b^{-k!}$ | $\{\delta_0\}$ | $0$ | Full rank, every Cauchy–Binet term positive, yet root $\to0$ | Rank-only countermodel (§7.4) |
| Phase 25 Lambert values with proved $D^+<1$ (`GF-42` B1.3 nonnegative families; signed families only for $k\ge k_0$, per Stage 0) | Unknown | Unknown | **New corollary**: $\limsup\lvert S_N(1)\rvert<1$ and $\liminf\det G_{N,2}(1)>0$ (Theorem 6.2) | Transition-density proofs are compatible with singular limits |

For $E_2/3$, `GF-03` gives $\{2^nE_2\}\to0$ circularly along a density-one set of $n$. Writing $2^nE_2=M_n+\varepsilon_n$ with $\varepsilon_n\to0$ along that set, $\{2^nE_2/3\}$ is within $\lvert\varepsilon_n\rvert/3$ of $\{M_n/3\}\in\{0,\frac13,\frac23\}$. So every limit measure is carried by these three points, and $a_*=0$ by Proposition 2.7. Theorem 6.3 then gives $\det G_{N,4}(1)\to0$.

---

## 5. Track A5: quantitative determinant rates for solved normal families

### 5.1 The exact Koksma constant

**Theorem 5.1 (A5.1; Paper proof, Finite certificate).** For every finite point set $(t_n)_{n<N}\subset[0,1)$ and every nonzero integer $h$,
$$\Bigl\lvert\frac1N\sum_{n<N}e(ht_n)\Bigr\rvert\le2\lvert h\rvert\,D_N\qquad\text{and}\qquad\Bigl\lvert\frac1N\sum_{n<N}e(ht_n)\Bigr\rvert\le4\lvert h\rvert\,D_N^* .$$
The constant $2$ is **sharp**: $\sup\lvert S_N(h)\rvert/(\lvert h\rvert D_N)=2$ over all finite point sets, for each fixed $h$. The classical Koksma bound $2\pi\lvert h\rvert D_N^*$ is valid but not sharp.

*Proof.*

- *Integration by parts.* Let $f(t)=e(ht)$. Since $f(1)=f(0)$, $f(t_n)=f(0)+\int_0^1\mathbf 1[s<t_n]f'(s)\,ds$. Averaging, and using $\int_0^1s f'(s)\,ds=1$,
$$S_N(h)=-\int_0^1R(s)f'(s)\,ds,\qquad R(s)=\mu_N([0,s))-s .$$
  (The value at the finitely many atoms is irrelevant.)
- *Recentring.* Because $\int_0^1f'=0$, $R$ may be replaced by $R-\kappa$ for any constant $\kappa$. So $\lvert S_N(h)\rvert=2\pi\lvert h\rvert\,\lvert\int_0^1(R-\kappa)e(hs)\,ds\rvert$.
- *Real-valued test functions.* For real $g$, $\lvert\int g\,e(hs)\rvert=\max_\phi\int g(s)\cos(2\pi hs-\phi)\,ds\le\lVert g\rVert_\infty\int_0^1\lvert\cos(2\pi hs-\phi)\rvert\,ds=\frac2\pi\lVert g\rVert_\infty$, because $[0,1]$ contains $\lvert h\rvert$ full periods.
- *Conclusion.* With $\kappa=\frac12(\sup R+\inf R)$, Lemma 0.1 gives $\lVert R-\kappa\rVert_\infty=D_N/2$, hence $\lvert S\rvert\le2\pi\lvert h\rvert\cdot\frac2\pi\cdot\frac{D_N}2=2\lvert h\rvert D_N$. With $\kappa=0$ we get $4\lvert h\rvert D_N^*$.

*Sharpness.* For small $\delta>0$ let
$$\rho_\delta=\delta\,\delta_0+\mathbf 1_{\{\lvert t-\frac12\rvert>\delta/2\}}\,dt .$$
Every arc has $\lvert\rho(J)-\lambda(J)\rvert\le\delta$, since the excess sits at one atom and the deficit on one arc. So $D(\rho_\delta)=\delta$, while $\hat\rho_\delta(1)=\delta+\frac{\sin\pi\delta}{\pi}$. The ratio $1+\frac{\sin\pi\delta}{\pi\delta}$ tends to $2$. Pulling $\rho$ back along $M_h$ (the average of the $h$ translates of $\rho(h\cdot)$) divides the discrepancy by $h$ and preserves the coefficient, so the same holds for every $h$. Discretize by $N$ points. ∎

*Finite certificate (section A5).* The script uses $M=1000$ grid sites $j/M$ with unit multiplicity, removes the 51 sites with $\lvert j/M-\frac12\rvert\le\frac1{40}$, and places 51 extra points at $0$. Then:

- $D_N=0.052$ exactly, and $\lvert h\rvert D_N=0.052$ exactly for the unwound configurations used for $h=2,3$.
- Using only $\cos y\ge1-y^2/2$, $\pi<22/7$ and $\sum_j\cos(2\pi j/M)=0$: $\mathrm{Re}\,S_N(1)\ge0.101781$. The exact rational lower bound is $0.1017817\ldots$, which would round up to $0.101782$; the script asserts $\ge0.101781$ (and $<0.101782$) as `Fraction` comparisons.
- Hence $\lvert S\rvert/(\lvert h\rvert D_N)>1.957$ for $h=1,2,3$, asserted exactly in the script.

Further, $\lvert S(h)\rvert\le2\lvert h\rvert D_N$ and $\le4\lvert h\rvert D_N^*$ are verified exactly on all 1,702 multiplicity configurations supported on $\frac1Q\mathbb{Z}$ with $Q\in\{3,4,6\}$ (where all cosines are rational), for $h=1,\dots,6$.

### 5.2 A linear-in-$r$ Toeplitz bound

**Theorem 5.2 (A5.2; Paper proof, Finite certificate).** For every $N$, $r\ge1$ and $h\ne0$,
$$\lVert G_{N,r}(h)-I\rVert_{\rm op}\le\pi(r-1)\,D(\nu_N)\le\pi\lvert h\rvert(r-1)\,D_N .$$
Thus every eigenvalue of $G_{N,r}(h)$ lies in $[1-\pi\lvert h\rvert(r-1)D_N,\ 1+\pi\lvert h\rvert(r-1)D_N]$.

*Proof.* Let $a\in\mathbb{C}^r$ with $\lVert a\rVert=1$. Shifting frequencies does not change $\lvert q\rvert^2$, so $a^*Ga=\int\lvert q\rvert^2d\nu_N$ with $q(\theta)=\sum_ja_je((j-\frac{r-1}2)\theta)$ and $\int\lvert q\rvert^2d\lambda=1$.

- The integration by parts of Theorem 5.1 applies to the real periodic $C^1$ function $f=\lvert q\rvert^2$ and gives $\lvert\int f\,d\nu_N-\int f\,d\lambda\rvert\le\frac{D(\nu_N)}2\int_0^1\lvert f'\rvert$.
- $\int\lvert f'\rvert\le2\lVert q\rVert_2\lVert q'\rVert_2\le2\pi(r-1)$, since the centred frequencies have absolute value at most $(r-1)/2$.
- For the second inequality, take first $h>0$. Then $M_h^{-1}(J)$ is a union of $h$ half-open arcs of length $\lambda(J)/h$, so $D(\nu_N)\le hD_N$ (Lemma 0.1(2)). For $h<0$ the $\lvert h\rvert$ preimage arcs have the form $(a,a']$. Their discrepancy is also at most $D_N$: apply Lemma 0.1(2) to $[a+\varepsilon,a'+\varepsilon)$ and let $\varepsilon\downarrow0$, which is legitimate because $\mu_N$ has finitely many atoms. Alternatively, $G_{N,r}(-h)=\overline{G_{N,r}(h)}$ has the same spectrum as $G_{N,r}(h)$. ∎

For comparison, the entrywise route gives a weaker bound. Using $\lvert S_N(kh)\rvert\le2k\lvert h\rvert D_N$ and Gershgorin, $\max_j\sum_k\lvert k-j\rvert=r(r-1)/2$, so $\lVert G-I\rVert\le\lvert h\rvert D_Nr(r-1)$. The brief's form $\pi\lvert h\rvert D_Nr(r-1)$ is what Koksma's constant $2\pi$ gives. Theorem 5.2 shows that the entries cannot all be extremal at once, and gains a factor $r$.

The script certifies $\lVert G_{N,r}(h)-I\rVert<3.14159\,\lvert h\rvert(r-1)D_N$ exactly. It shows that $\beta I\pm(G-I)$ is positive definite by Sylvester's criterion over $\mathbb{Q}(i)$, for all 1,125 cases with $Q=4$ grid configurations, $N\le5$, $h\le3$ and $2\le r\le4$. It also checks the Frobenius identity $\lVert G-I\rVert_F^2=2\sum_{k=1}^{r-1}(r-k)\lvert S_N(kh)\rvert^2$ and $\sum_{k<r}(r-k)k^2=r^2(r^2-1)/12$.

### 5.3 Two-sided Fourier-energy determinant estimate

**Theorem 5.3 (Paper proof).** Let $E=G_{N,r}(h)-I$ and suppose $\lVert E\rVert\le\eta<1$. Then
$$-\frac{\lVert E\rVert_F^2}{2(1-\eta)}\le\log\det G_{N,r}(h)\le-\frac{\lVert E\rVert_F^2}{2(1+\eta)},\qquad \lVert E\rVert_F^2=2\sum_{k=1}^{r-1}(r-k)\lvert S_N(kh)\rvert^2 .$$
Equivalently,
$$-\frac1r\log\det G_{N,r}(h)=\theta\sum_{k=1}^{r-1}\Bigl(1-\frac kr\Bigr)\lvert S_N(kh)\rvert^2,\qquad \theta\in\Bigl[\frac1{1+\eta},\frac1{1-\eta}\Bigr].$$
So, while $\lVert E\rVert\le\eta<1$, the normalized determinant deficit **is**, to within the factor $\theta$, the Fejér-weighted Fourier energy of the first $r-1$ harmonics. Without that hypothesis the two quantities can separate completely (Corollary 5.4, item 3 of the converse). In particular,
$$\Bigl(\det G_{N,r}\Bigr)^{1/r}\ge\exp\Bigl(-\frac{\lVert E\rVert^2}{2(1-\lVert E\rVert)}\Bigr).$$

*Proof.* For $\lvert\lambda\rvert\le\eta$, $\lambda-\frac{\lambda^2}{2(1-\eta)}\le\log(1+\lambda)\le\lambda-\frac{\lambda^2}{2(1+\eta)}$: both differences vanish at $0$ and have derivatives of the correct sign on each side. Sum over the eigenvalues of $E$, using $\operatorname{tr}E=0$ (zero diagonal) and $\sum\lambda_i^2=\lVert E\rVert_F^2\le r\lVert E\rVert^2$. ∎

**Corollary 5.4 (general rate dependence; Paper proof).** Suppose $D_N(x;b)\le\varepsilon(N)\to0$, and let $r(N)\ge1$ satisfy $\pi\lvert h\rvert(r(N)-1)\varepsilon(N)\le\eta_N\le\eta<1$. Then
$$1-\bigl(\det G_{N,r(N)}(h)\bigr)^{1/r(N)}\le\frac{\eta_N^2}{2(1-\eta)} .$$
In particular the root tends to $1$ for **every** $r(N)=o(1/\varepsilon(N))$.

**Converse, restricted (Paper proof, Finite certificate).** Theorem 5.3 is two-sided only while $\lVert E\rVert_{\rm op}<1$, and the converse holds only in that regime. Write $\mathcal E_{N,m}=\sum_{k=1}^{m-1}(1-k/m)\lvert S_N(kh)\rvert^2=\lVert G_{N,m}(h)-I\rVert_F^2/(2m)$ for the Fejér-weighted Fourier energy at dimension $m$.

1. *Bounded-norm regime.* If $\limsup_N\lVert G_{N,r(N)}(h)-I\rVert_{\rm op}<1$, then $(\det G_{N,r(N)}(h))^{1/r(N)}\to1$ iff $\mathcal E_{N,r(N)}\to0$. For all large $N$, Theorem 5.3 applies with one fixed $\eta<1$, and $-\frac1r\log\det G_{N,r}=\theta_N\,\mathcal E_{N,r}$ with $\theta_N\in[\frac1{1+\eta},\frac1{1-\eta}]$.
2. *Sub-dimensions, unconditionally.* If $(\det G_{N,r(N)}(h))^{1/r(N)}\to1$, then $\mathcal E_{N,m(N)}\to0$ for every $1\le m(N)\le r(N)$ with $\limsup_N\lVert G_{N,m(N)}(h)-I\rVert_{\rm op}<1$. Indeed, Corollary 1.5(2) and Hadamard's inequality give $(\det G_{N,r(N)})^{1/r(N)}\le(\det G_{N,m(N)})^{1/m(N)}\le1$. So the root at dimension $m(N)$ also tends to $1$, and item 1 applies there. For every **fixed** $m$ (with $m\le r(N)$ eventually) the norm hypothesis is automatic. Then $\det G_{N,m}\to1$, and the eigenvalues of $G_{N,m}$ lie in the compact set $\{\lambda\in[0,m]^m:\sum_i\lambda_i=m\}$, on which $\prod_i\lambda_i=1$ only at $\lambda=(1,\dots,1)$ (AM–GM). So $\lVert G_{N,m}-I\rVert_{\rm op}\to0$, and in particular $S_N(kh)\to0$ for every fixed $k\ge1$.
3. *The unrestricted converse is false.* The energy at the full dimension $r$ need not tend to $0$.

*Counterexample (Paper proof, Finite certificate).* Fix $m\ge2$ and put $r=m^4$, $N=2m^4$, $K=m^3$ and $\alpha=K/N=\frac1{2m}$. Take the $N$ unimodular points consisting of $K$ copies of $1$ together with the $N-K=2m^4-m^3$ roots of $z^{N-K}=1$. For $1\le k\le r-1<N-K$ the roots sum to $0$ at frequency $\pm k$, so $S_N(\pm k)=K/N=\alpha$ and
$$G_{N,r}(1)=(1-\alpha)I_r+\alpha J_r .$$
By Proposition 4.1 and Hadamard's inequality,
$$1\ge\bigl(\det G_{N,r}(1)\bigr)^{1/r}=(1-\alpha)^{1-1/r}\bigl(1+(r-1)\alpha\bigr)^{1/r}\ge1-\alpha=1-\frac1{2m}\to1,$$
whereas
$$\mathcal E_{N,r}=\sum_{k=1}^{r-1}\Bigl(1-\frac kr\Bigr)\lvert S_N(k)\rvert^2=\frac{r-1}2\,\alpha^2=\frac{m^4-1}{8m^2}\to+\infty .$$
Here $\lVert E\rVert_{\rm op}=(r-1)\alpha=\frac{m^4-1}{2m}\to\infty$, so Theorem 5.3 does not apply. The spectrum of $E$ is $-\alpha$ with multiplicity $r-1$ and $(r-1)\alpha$ once. The single large eigenvalue costs only $\frac1r\log(1+(r-1)\alpha)\to0$ in the log-root, but it carries almost all of $\lVert E\rVert_F^2/(2r)=\mathcal E_{N,r}$. At the sub-dimension $m$, by contrast, $\lVert G_{N,m}(1)-I\rVert=(m-1)\alpha<\frac12$ and $\mathcal E_{N,m}=\frac{(m-1)\alpha^2}2\le\frac1{8m}\to0$, as item 2 requires. Script section A5 verifies all of this exactly for $2\le m\le6$. For $m\le3$ it also checks $N\,S_N(k)=K$ in $\mathbb{Z}[\zeta_{N-K}]$ for every $1\le k<r$ and the $r\times r$ determinant by exact elimination.

*Orbit realization (Paper proof).* The same separation occurs along the orbit of a single normal number, for a schedule $r(N)\to\infty$ whose root tends to $1$ along **all** $N$. Choose integers $r_j\ge8$ with $r_j\to\infty$, put $\alpha_j=r_j^{-1/3}\le\frac12$ and $k_j=s_j=\lceil3\log_br_j\rceil$, so that $r_jb^{-k_j}\le r_j^{-2}$ and $r_j^2b^{-s_j}\le r_j^{-1}$. Stage $j$ of the digits of $x$ is a block of complete copies of a de Bruijn cycle $\beta_{k_j}$ of order $k_j$, of total length $A_j$, followed by $Z_j=\lfloor\alpha_j(N_{j-1}+A_j)/(1-\alpha_j)\rfloor$ zeros, and $N_j=N_{j-1}+A_j+Z_j$. Let $r_j$ grow so slowly that $b^{k_j}+s_j\le N_{j-1}/j$ for all large $j$, and then take $A_j\ge j\,(r_jN_{j-1}+r_j^2s_j)$.

- *Gram matrix at $N_j$.* Replace each orbit point of stage $j$ by the de Bruijn rotation point it shadows, or by $0$ inside the zero run. Every position with at least $s_j$ digits left in its block moves by at most $b^{-s_j}$, and at most $2s_j$ positions move by at most $\frac12$. By Lemma 5.6 this changes $G_{N_j,r_j}(1)$ by at most $\pi r_j^2(b^{-s_j}+s_j/N_j)$ in norm. The modified matrix is $\frac{N_{j-1}}{N_j}G^{\rm old}+\frac{A_j}{N_j}G^{\rm dB}+\alpha'_jJ$ with $\alpha'_j=Z_j/N_j=\alpha_j+O(1/N_j)$. Here $G^{\rm dB}$ is the Gram matrix of the $b^{k_j}$ rotation points, which lie one in each $b$-adic interval of length $b^{-k_j}$. That point set has discrepancy at most $2b^{-k_j}$, so the proof of Theorem 5.2, which applies to any finite point set, gives $\lVert G^{\rm dB}-I\rVert\le2\pi(r_j-1)b^{-k_j}$. Also $\lVert G^{\rm old}-I\rVert\le r_j$. Hence $G_{N_j,r_j}(1)=(1-\alpha'_j)I+\alpha'_jJ+\mathrm{Err}_j$ with
$$\lVert\mathrm{Err}_j\rVert\le\eta_j:=\frac{r_jN_{j-1}}{N_j}+2\pi r_jb^{-k_j}+\pi r_j^2\Bigl(b^{-s_j}+\frac{s_j}{N_j}\Bigr)\to0 .$$
- *Root and energy.* $(\det G_{N_j,r_j}(1))^{1/r_j}\ge\lambda_{\min}\ge1-\alpha'_j-\eta_j\to1$. With $E=\alpha'_j(J-I)+\mathrm{Err}_j$, $\lVert E\rVert_F\ge\alpha'_j\sqrt{r_j(r_j-1)}-\sqrt{r_j}\,\eta_j$. So $\mathcal E_{N_j,r_j}=\lVert E\rVert_F^2/(2r_j)\ge\frac12(\alpha'_j\sqrt{r_j-1}-\eta_j)^2\to\infty$, because $\alpha_j^2r_j=r_j^{1/3}$.
- *Normality.* Zero runs occupy a vanishing fraction of every prefix. For $N$ in or after the zero run of stage $j$ the current run has length $Z_j\le2\alpha_jN$, and earlier runs total $o(N_{j-1})$ because $N_i\ge iN_{i-1}$. A complete de Bruijn cycle of order $k\ge L$ contains every word of length $L$ exactly $b^{k-L}$ times. Partial cycles and block boundaries contribute $O(b^{k_j}+jL)=o(N)$. So every word of length $L$ has frequency $b^{-L}$, as in Proposition 3.5.
- *Schedule.* Put $r(N_j)=r_j$ and $r(N)=\rho(N)$ for all other $N$, where $\rho$ is an optimal schedule for $x$ (Theorem 3.1 with $a_*=1$). Then $r(N)\to\infty$ and the root tends to $1$ along all $N$, while $\mathcal E_{N_j,r(N_j)}\to+\infty$. ∎

So beyond the bounded-norm regime the determinant root controls the Fejér energy only at those sub-dimensions where $G-I$ remains a strict contraction, not at the dimension $r$ itself.

**Corollary 5.5 (Stoneham numbers; External input `ST-28`; control, not a new proof).** Let $b,c\ge2$ be coprime with $c>2$. By `ST-28` (degree one; Vandehey's theorem as external input), the Stoneham number $\alpha=\alpha(b,c)$ satisfies
$$D_N(\alpha;b)\le C(b,c)\,N^{-1/2}(1+\log N)^2 .$$
Hence $\lVert G_{N,r}(h)-I\rVert\le\pi\lvert h\rvert C(r-1)N^{-1/2}(1+\log N)^2$, and:

- **The brief's schedule $r=\lfloor N^{1/5}\rfloor$:** $\lVert E\rVert=O(N^{-3/10}(\log N)^2)$, so $1-(\det G_{N,r})^{1/r}=O(N^{-3/5}(\log N)^4)$. The claim holds with this explicit rate.
- **Improved range:** for **every** $r(N)=o(N^{1/2}(1+\log N)^{-2})$ the root tends to $1$. If $r(N)\le\kappa N^{1/2}(1+\log N)^{-2}$ with $\pi\lvert h\rvert C\kappa\le\frac12$, the root is at least $e^{-(\pi\lvert h\rvert C\kappa)^2}$.
- **Polynomial images:** for $P(\alpha)$ with a polynomial $P$ of degree $d$ covered by `ST-28`, $D_N\ll N^{-\delta_d}$ gives the range $r=o(N^{\delta_d})$.

These are consequences of the **known** normality of Stoneham numbers. They do not prove normality independently. They identify the property that makes the determinant method work, namely a power-saving discrepancy, and they quantify the admissible dimension.

### 5.4 Complete rational orbit cancellation and shells

For a rational $a/Q$ with $\gcd(a,Q)=1$ and $b$ of multiplicative order $P$ modulo $Q$, full-period sums are exact character sums:
$$\sum_{n<P}e(kb^na/Q)=\sum_{u\in a\langle b\rangle}e(ku/Q).$$

- If $b$ is a primitive root modulo a prime $Q$, the sum is $-1$ for $Q\nmid k$. So, for $Q\nmid h$ (e.g. $h=1$) and $r\le Q$, $G_{P,r}(h)=(1+\beta)I-\beta J$ with $\beta=1/(Q-1)$: every off-diagonal frequency $(k-j)h$ has $0<\lvert k-j\rvert<Q$, hence $Q\nmid(k-j)h$. This is Proposition 4.1 with $\alpha=-\beta<0$.
- For prime powers $Q=p^K$ with $b$ a primitive root, the full-period sums are the Ramanujan sums $c_{p^K}(k)$. These vanish unless $p^{K-1}\mid k$, so $G_{P,r}(h)=I$ **exactly** for $r\le p^{K-1}/\lvert h\rvert$.

The script verifies the prime case in $\mathbb{Z}[\zeta_Q]$ for $(Q,b)\in\{(5,2),(7,3),(11,2),(13,2)\}$, including the determinant at $r=3$ computed directly in $\mathbb{Z}[\zeta_Q]$.

Along Stoneham shells the orbit follows such full periods up to exponentially small tails. This suggests that at **shell-aligned** $N$ the admissible dimension could reach $r\approx N/\log N$: each shell's Toeplitz matrix is $I$ up to frequencies $c^{K'}$, and a weighted sum over shells gives $\lVert G-I\rVert\lesssim r\log N/N$. **This is a heuristic, recorded as Open.** It is not used anywhere, and the prefix-uniform statement is Corollary 5.5.

### 5.5 Approximation stability and dimension dependence

**Lemma 5.6 (approximation stability; Paper proof).** If $\lVert t_n-t_n'\rVert_{\mathbb{T}}\le\varepsilon_n$ and $\bar\varepsilon=\frac1N\sum_n\varepsilon_n$, then
$$\lVert G_{N,r}(h)-G'_{N,r}(h)\rVert\le\pi\lvert h\rvert r(r-1)\,\bar\varepsilon .$$

*Proof.* Entries change by at most $2\pi\lvert h\rvert\lvert k-j\rvert\bar\varepsilon$; apply Gershgorin with $\max_j\sum_k\lvert k-j\rvert=r(r-1)/2$. ∎

For $\ln2$ with BBP models, $2^n\ln2\equiv s_n+T_n\pmod1$, i.e. $\lVert\{2^n\ln2\}-\{s_n\}\rVert_{\mathbb{T}}\le T_n$, with $0<T_n\le\frac1{n+1}$ (note that $\{s_n\}+T_n$ may exceed $1$). So $\bar\varepsilon\le(1+\log N)/N$, and the model Gram matrix of the rationals $\{s_n\}$ differs from the true one by at most $\pi\lvert h\rvert r^2(1+\log N)/N$. Models are therefore faithful for $r=o((N/\log N)^{1/2})$. The difficulty is not approximation; it is that the model points have denominators $Q_N$ with $\log Q_N\sim N$ (§7.3).

**Theorem 5.7 (random-point law; Paper proof, Finite certificate).** Let $z_0,\dots,z_{N-1}$ be independent and uniform on $\mathbb{T}$, or uniform on $\mu_Q$ with $Q\ge r$. Then
$$\mathbb E\det G_{N,r}=\prod_{j=0}^{r-1}\Bigl(1-\frac jN\Bigr)\qquad(1\le r\le N).$$
Moreover, for points uniform on $\mathbb{T}$, $\mathbb E\log\det G_{N,N}=-N\log N$, and $\det G_{N,N}\le1$ with equality iff the points form a rotated regular $N$-gon.

*Proof.*

- By Cauchy–Binet (Theorem 7.1), $\mathbb E\det G_{N,r}=N^{-r}\binom Nr\,\mathbb E\lvert V(z_1,\dots,z_r)\rvert^2$.
- $\mathbb E\lvert V\rvert^2=\sum_{\sigma,\tau}\operatorname{sgn}(\sigma\tau)\prod_a\mathbb E\,z_a^{\sigma(a)-\tau(a)}=r!$, because the monomials $z^j$ ($j<r$) are orthonormal on $\mathbb{T}$, and also on $\mu_Q$ when $Q\ge r$.
- For $r=N$: $\det G_{N,N}=N^{-N}\prod_{i<j}\lvert z_i-z_j\rvert^2$ and $\mathbb E\log\lvert z_i-z_j\rvert^2=\int_0^1\log(4\sin^2\pi u)\,du=0$.
- For the extremal statement, Hadamard's inequality gives $\det G_{N,N}\le1$, with equality iff $G=I$. That means $\sum_nz_n^k=0$ for $0<k<N$, i.e. the $z_n$ are the roots of $z^N=c$. ∎

The script checks the identity exactly by enumerating all $4^N$ configurations on $\mu_4$ for $N\le6$ and $r\le\min(N,4)$.

*Interpretation (dimension dependence).*

- $r\le N$ is forced by rank.
- $r=o(1/D_N)$ suffices for normal $x$ (Corollary 5.4).
- For random points, $r=o((N/\log\log N)^{1/2})$ suffices almost surely, by Chung's law of the iterated logarithm for $D_N$.
- $r=N$ fails, since the expected log-root is $-\log N$, although the expected determinant $\prod(1-j/N)$ is not small for $r=o(N)$.
- The window $N^{1/2}\lesssim r\lesssim N$ is **Open**.

---

## 6. Track A6: regularization and weaker positivity certificates

### 6.1 Regularized determinants carry no new asymptotic information

**Theorem 6.1 (A6.1; Paper proof, Finite certificate).** Let $\mu$ be $T_b$-invariant, $\nu=(M_h)_*\mu$ and $0<t<1$. For every $m$,
$$\det\bigl((1-t)T_m(\nu)+tI\bigr)^{1/m}\ge t+(1-t)a(\mu),$$
and the limit as $m\to\infty$ equals $t+(1-t)a(\mu)$. Consequently, with $G^{(t)}_{N,r}=(1-t)G_{N,r}+tI$,
$$\sup_{r(N)\to\infty}\liminf_N\bigl(\det G^{(t)}_{N,r(N)}(h)\bigr)^{1/r(N)}=t+(1-t)a_* .$$

*Proof.* $(1-t)T_m(\nu)+tI=T_m((1-t)\nu+t\lambda)$, and $(1-t)\nu+t\lambda=(t+(1-t)a(\mu))\lambda+(1-t)\nu_s$ by Lemma 2.3. This is the coordinator's computation, now justified. Apply Proposition 2.4, then repeat the proof of Theorem 3.1. ∎

The rate is **affine** in $a_*$. A regularized lower bound $c_t$ yields exactly $a_*\ge(c_t-t)/(1-t)$, so only a strict improvement over the floor $t$ carries information, and that information is again $a_*$. Regularization therefore **cannot** detect singular measures.

What it does buy is finite-dimensional **stability**. If $A,B\succeq tI$, then
$$\tfrac1r\lvert\log\det A-\log\det B\rvert\le\lVert A-B\rVert/t ,$$
because $\frac{d}{ds}\log\det(B+s(A-B))=\operatorname{tr}((B+s(A-B))^{-1}(A-B))$. So changing the Fourier coefficients by $\Delta c_k$ moves the regularized log-root by at most $\frac2t\sum_{k<r}\lvert\Delta c_k\rvert$, which is Lipschitz, unlike the unregularized log-root near singular matrices. The finite regularized bound is $\frac1r\log\det G^{(t)}\ge\log(t+(1-t)\lambda_{\min}(G))$.

### 6.2 The 2×2 determinant characterizes $D^+<1$ in every radix

**Theorem 6.2 (A6.2; Paper proof, Finite certificate).** For every finite point set, writing $S=S_N(1)$ and $D=D_N$:

1. For every $\ell\in(0,\frac12]$, $D\ge1-\ell-\frac{1-\lvert S\rvert}{4\ell^2}$. Hence, if $1-\lvert S\rvert\le\frac14$,
$$D_N\ge1-\tfrac32\Bigl(\tfrac{1-\lvert S_N(1)\rvert}2\Bigr)^{1/3}.$$
2. If $D\ge1-\delta$ with $0\le\delta\le\frac12$, then $\lvert S\rvert\ge(1-\delta)\cos\pi\delta-\delta\ge1-2\delta-5\delta^2$.
3. $\lvert S\rvert\le2D$ (Theorem 5.1).

Consequently, for every $x$ and every radix $b$, with $\sigma=\limsup_N\lvert S_N(1)\rvert$:
$$1-\tfrac32\Bigl(\tfrac{1-\sigma}2\Bigr)^{1/3}\le D^+(x;b)\le1-\delta_\sigma,\qquad \delta_\sigma=\frac{\sqrt{1+5(1-\sigma)}-1}5 ,$$
where the left inequality is valid when $1-\sigma\le\frac14$. In particular:
$$D^+(x;b)<1\iff\limsup_N\lvert S_N(1)\rvert<1\iff\liminf_N\det G_{N,2}(1)>0,$$
$$x\in K_b\iff\lvert S_N(1)\rvert\to1\iff\det G_{N,2}(1)\to0 .$$
The same statements with $\liminf$ and $\limsup$ exchanged characterize $D^-<1$.

*Proof.*

1. Choose $s$ with $\lvert S\rvert=\frac1N\sum\cos2\pi(t_n-s)$, and let $A=[s-\frac\ell2,s+\frac\ell2)$. Points outside $A$ have $1-\cos2\pi(t-s)\ge1-\cos\pi\ell\ge4\ell^2$. The last inequality holds on $[0,\frac12]$: $f(\ell)=1-\cos\pi\ell-4\ell^2$ satisfies $f(0)=f'(0)=0$ and $f(\frac12)=0$, and $f''=\pi^2\cos\pi\ell-8$ changes sign once, from positive to negative. So $\mu_N(A^c)\le(1-\lvert S\rvert)/(4\ell^2)$, and $D\ge\mu_N(A)-\lambda(A)$ by Lemma 0.1(2). Taking $\ell^3=(1-\lvert S\rvert)/2$ optimizes the bound.
2. As in Phase 23 Proposition 5.1. Some half-open arc of length at most $\delta+\varepsilon'$ carries mass at least $1-\delta-\varepsilon'$: either the extremal interval itself, or the complement of a long, nearly empty one. Points in it satisfy $\mathrm{Re}\,e(t-c)\ge\cos\pi(\delta+\varepsilon')$; let $\varepsilon'\to0$. Then use $\cos y\ge1-y^2/2$ and $\pi^2/2<5$.
3. *Asymptotics.* Apply items 1 and 2 along subsequences. If $D^+>1-\delta_\sigma$, item 2 gives $\limsup\lvert S\rvert>1-2\delta_\sigma-5\delta_\sigma^2=\sigma$, a contradiction. Finally $\det G_{N,2}(1)=1-\lvert S_N(1)\rvert^2$. ∎

**On novelty.** The argument is base-free: it is a statement about point sets. So the extension from base 2 (Phase 23) to every radix is immediate. What is new here:

- the optimized cube-root converse, which in Phase 23 had the form $1-2\delta-\eta/(1-\cos2\pi\delta)$;
- the determinant formulation;
- the $K_b$ and $D^-$ versions;
- the identification with fixed-point Diracs (Lemma 2.6);
- the hierarchy of Theorem 6.3.

The test $\limsup\mathrm{Re}\,S_N(b-1)<1$ also implies $D^+<1$, since $1-\cos2\pi(b-1)t$ vanishes exactly at the fixed points, but for $b\ge3$ it is not necessary. Take the point whose base-3 digits are $0\,1\,00\,11\,000\,111\cdots$, i.e. runs $0^k1^k$ with slowly growing lengths $L_k=k$. At precision $3^{-s}$ only $O(s)$ positions per run are uncontrolled, and there are $O(\sqrt N)$ runs up to $N$, so $C_3(x)=\{\frac12(\delta_0+\delta_{1/2})\}$. (With exponentially growing run lengths the empirical measures would oscillate, and $C_3(x)$ would not be a singleton.) Then $\mathrm{Re}\,S_N(2)\to1$, but $D_N\to\frac12$.

**Corollary 6.2.1 (explicit thresholds for $\ln2$; Paper proof, Finite certificate).** Let $\sigma=\limsup_N\lvert\frac1N\sum_{n<N}e(2^n\ln2)\rvert$.

- If $\sigma\le0.99979995$, then $D^+(\ln2;2)\le0.9999$. Here $0.99979995=1-2\delta-5\delta^2$ at $\delta=10^{-4}$, and the script checks that it is at most the Phase 23 form $(1-\delta)(1-(22\delta/7)^2/2)-\delta$.
- Conversely, $D^+(\ln2;2)\le0.9999$ forces $\sigma\le1-\frac{16}{27}\cdot10^{-12}$, from item 1 with $\ell=2\delta/3$.

So the classical target is equivalent, up to these explicit constants, to a **fixed saving** in a single Weyl sum. The known saving is only $\mathrm{Re}\,S_N(1)\le1-(1+o(1))\frac{\log N}{N\log\mu}$, with $\mu=3.5746$ (Phase 23 §5.4; Marcovecchio 2009). $D^+(\ln2;2)\le0.9999$ remains **Open**.

### 6.3 The fixed-dimension hierarchy

**Theorem 6.3 (A6.3; Paper proof, Finite certificate).** For every $m\ge1$,
$$\liminf_N\det G_{N,m}(1)=\min_{\mu\in C_b(x)}D_m(\mu),$$
and $D_m(\mu)=0$ iff $\#\operatorname{supp}\mu\le m-1$. Hence $\liminf_N\det G_{N,m}(1)>0$ iff no limit measure is supported on fewer than $m$ points. Such invariant measures are exactly the convex combinations of periodic-orbit measures with fewer than $m$ points in total.

- $m=2$: exclusion of the fixed-point Diracs, i.e. $D^+<1$ (Theorem 6.2, Lemma 2.6).
- All $m$: $C_b(x)$ contains no finitely supported measure.

*Proof.* $D_m(\mu)=0$ iff some nonzero $q$ of degree less than $m$ has $\int\lvert q\rvert^2d\mu=0$, iff $\mu$ is carried by the at most $m-1$ zeros of $q$. Conversely, if $\#\operatorname{supp}\mu\le m-1$, take $q$ vanishing on the support. The $\liminf$ equals the minimum over limit points, by continuity and compactness. ∎

So fixed-dimension positivity, at **every** level, detects the absence of finitely supported limits, and it can hold for singular measures (biased Bernoulli: $D_m(\mu_p)>0$ for every $m$). The growing-dimension root detects Lebesgue mass. Both are exact, and they answer different questions. Examples: $E_2/3$ has level 2 positive and level 4 zero. The script verifies exactly in $\mathbb{Z}[\zeta_3]$ that the two-point orbit of $1/3$ gives $\det G_2\ne0=\det G_3$.

### 6.4 A finite interval-mass certificate

**Theorem 6.4 (A6.4; Paper proof, Finite certificate).** If $\lambda_{\min}(G_{N,r}(1))\ge\gamma>0$, then for every half-open arc $J$ and every $\delta>0$,
$$\mu_N(J)\ge\gamma\bigl(\lambda(J)-2\delta\bigr)-\frac1{2r\delta},\qquad\text{hence}\qquad D_N\le1-\gamma+2\sqrt{\gamma/r} .$$
This holds at the finite index $N$, with no limit taken.

*Proof.* Let $F_r(u)=\frac1r\lvert\sum_{j<r}e(ju)\rvert^2$ be the Fejér kernel.

- *Pointwise lower bound.* For each $s$, $(F_r*\mu_N)(s)=a^*G_{N,r}a$ with $a_j=r^{-1/2}e(-js)$ and $\lVert a\rVert=1$. So $F_r*\mu_N\ge\gamma$ pointwise.
- *Integrate over a shrunken arc.* Let $I$ be $J$ shrunk by $\delta$ at both ends. Then $\gamma\lambda(I)\le\int(F_r*\mathbf 1_I)\,d\mu_N$.
- *Fejér tail.* $F_r*\mathbf 1_I\le1$ everywhere, and $F_r*\mathbf 1_I\le\int_{\lvert u\rvert\ge\delta}F_r\le\frac1{2r\delta}$ off the open $\delta$-neighbourhood of $I$, which is contained in $J$. The tail bound uses $F_r(u)\le(4ru^2)^{-1}$ on $\lvert u\rvert\le\frac12$.
- *Discrepancy.* Bound $\lambda(J)-\mu_N(J)$ and $\mu_N(J)-\lambda(J)=\lambda(J^c)-\mu_N(J^c)$ as in Lemma 2.5, and take $\delta=(4\gamma r)^{-1/2}$. ∎

The script checks the certificate exactly on 504 cases. In each, $\gamma$ is certified by Sylvester positivity of $G-\gamma I$ with $\gamma\in\frac1{32}\mathbb{Z}$, found by bisection, and the conclusion is verified in the squared form $(D-1+\gamma)_+^2\le4\gamma/r$.

**Determinant versus minimum eigenvalue at finite $N$.** A lower bound on $\det^{1/r}$ does not bound $\lambda_{\min}$, since a single small eigenvalue suffices to make $\lambda_{\min}$ small. It does bound Gram–Schmidt residuals at small indices: from $\prod_{j<r}d_j\ge c^r$, $d_j\le1$ and the monotonicity of $d_j$, we get $d_m\ge c^{r/(r-m)}$. Converting such residual (prediction-error) bounds into interval masses at finite $N$, through Christoffel-function estimates, is **Open** (§13).

**Positive trigonometric witnesses.** For a closed set $Z\subset\mathbb{T}$ and a trigonometric polynomial $P\ge0$ with $P^{-1}(0)=Z$, $\liminf_N\int P\,d\mu_N>0$ iff no limit measure is carried by $Z$. Three useful choices:

- $P=1-\cos2\pi(t-s)$: Theorem 6.2.
- $P=1-\cos2\pi(b-1)t$: $Z$ is the set of fixed points.
- $P=\prod_{\tau\in Z}(1-\cos2\pi(t-\tau))$: $Z$ is any finite union of periodic orbits.

Signed minorants of indicators form a different but related class. An example is the Phase 23 bound $\frac{c^2-c}2\le\mathbf 1_{[1/4,3/4]}$ with $c=\cos2\pi t$, which lower-bounds the binary transition density.

These certificates test **exclusion of finitely supported limits**. That is the mechanism behind the transition-density proofs of $D^+<1$ for the Lambert families (e.g. `GF-42`), and none of them requires a Lebesgue component.

---

## 7. Track A7: arithmetic and spectral limitations

### 7.1 Cauchy–Binet

**Theorem 7.1 (Paper proof, Finite certificate).** With $z_n=e(hb^nx)$,
$$\det G_{N,r}(h)=N^{-r}\sum_{0\le i_1<\cdots<i_r<N}\ \prod_{1\le j<k\le r}\lvert z_{i_j}-z_{i_k}\rvert^2 .$$
The sum is empty, and the determinant $0$, when $r>N$. For $r=2$: $1-\lvert S_N(h)\rvert^2=N^{-2}\sum_{i<j}\lvert z_i-z_j\rvert^2$, the mean squared pairwise distance (twice the circular variance).

*Proof.* $G=V^*V$, where $V$ is the $N\times r$ matrix with rows $N^{-1/2}(z_n^{\,j})_{j<r}$. Cauchy–Binet gives $\det(V^*V)=\sum_{\lvert I\rvert=r}\lvert\det V_I\rvert^2$, and $\det V_I=N^{-r/2}\prod_{j<k}(z_{i_k}-z_{i_j})$ is a Vandermonde determinant. ∎

The script verifies this exactly over $\mathbb{Q}(i)$ (40 random configurations) and in $\mathbb{Z}[\zeta_Q]$ for 15 rational orbits $(Q,b,a,h,N,r)$.

### 7.2 Cyclotomic structure: norms, Vandermonde divisibility, Galois averaging

**Proposition 7.2 (Paper proof, Finite certificate).** Let $x=a/Q$ and $z_n=\zeta_Q^{u_n}$ with $u_n\equiv hab^n\pmod Q$, and put $X=N^r\det G_{N,r}(h)$.

1. $X$ is an algebraic integer in $\mathbb{Q}(\zeta_Q)^+$. Each Galois conjugate $\sigma_c(X)$, $c\in(\mathbb{Z}/Q)^\times$, equals $N^r\det G_{N,r}$ for the conjugate configuration $\zeta^{cu_n}$, i.e. for the multiplier $x\mapsto cx$. So $0\le\sigma_c(X)\le N^r$, and $X$ is **totally nonnegative**.
2. $X\ne0$ iff the orbit has at least $r$ distinct points. Throughout, $\mathrm{Norm}(X)=N_{\mathbb{Q}(\zeta_Q)/\mathbb{Q}}(X)=\prod_{c\in(\mathbb{Z}/Q)^\times}\sigma_c(X)$ is the absolute norm from the full cyclotomic field, of degree $\varphi(Q)$. For $X\in\mathbb{Q}(\zeta_Q)^+$ and $Q>2$ it is the square of $N_{\mathbb{Q}(\zeta_Q)^+/\mathbb{Q}}(X)$. If $X\ne0$, then $\mathrm{Norm}(X)\in\mathbb{Z}_{\ge1}$, and the Liouville-type bound reads
$$\det G_{N,r}\ge N^{-r\varphi(Q)},$$
   a cost of $\varphi(Q)\log N$ per dimension in the log-root.
3. **Vandermonde divisibility.** For $Q=p$ prime, every nonzero Cauchy–Binet term is a product of $\binom r2$ factors $\lvert1-\zeta^d\rvert^2=(1-\zeta^d)(1-\zeta^{-d})$, each of valuation $2$ at $\mathfrak p=(1-\zeta_p)$. Hence $\mathfrak p^{r(r-1)}\mid X$ and $p^{r(r-1)}\mid\mathrm{Norm}(X)$.
4. **Galois-averaged lower bound.** If $X\ne0$, then $\prod_c\sigma_c(X)\ge p^{r(r-1)}$. That is, the geometric mean of $\det G_{N,r}$ over the multiplier family $\{cx\}$ is at least $N^{-r}p^{r(r-1)/(p-1)}$. This bound is attained when $N=r=p$ and the points are uniform: $X=p^p$, of valuation $p(p-1)$.
5. **Uniform roots.** $\sum_{I\subseteq\mathbb{Z}/Q,\ \lvert I\rvert=r}\prod_{a<c\in I}\lvert\zeta^a-\zeta^c\rvert^2=Q^r$ for $r\le Q$, because $G=I$ for the $Q$ points $\mu_Q$.

The script verifies items 1–5 exactly: norms are computed as $\mathrm{Res}(\Phi_Q,X)$ over $\mathbb{Q}$, item 5 is checked for all $Q\le9$ and $r\le Q$, and divisibility for $p\in\{5,7,11,13\}$.

**The barrier in Galois averaging.** Items 1–4 bound only the **geometric mean over the conjugate family** $\{cx\}$. Arithmetic positivity in the form $\mathrm{Norm}\ge1$ cannot single out the embedding corresponding to $x$, so a small individual determinant is entirely compatible with the norm bound.

### 7.3 The separation-cost barrier

**Proposition 7.3 (A7.3; Paper proof).** Suppose the orbit points have pairwise distances at least $s$ whenever they are distinct. For $Q$-th roots of unity, $s=2\sin(\pi/Q)\ge4/Q$. Let $M_r$ be the number of index sets $I$ of size $r$ with distinct points. Then
$$N^{-r}M_rs^{r(r-1)}\le\det G_{N,r}(h),\qquad\text{and}\qquad N^{-1}M_r^{1/r}s^{r-1}\le\frac er\,s^{r-1} .$$
So, when $s<1$, a lower bound $\det^{1/r}\ge c$ obtained from separation alone is possible only when
$$r-1\le\frac{\log(e/(rc))}{\log(1/s)} .$$
With the certified separation $s=4/Q$, which requires $Q>4$ for $s<1$, it is possible only when $r-1\le\log(e/(rc))/\log(Q/4)$.

The resulting **dichotomy is self-defeating**:

- A growing schedule gets nothing from separation unless $Q$ stays bounded.
- Bounded $Q$ forces $\operatorname{rank}\le Q$, hence $\det=0$ for $r>Q$ (Proposition 1.6).

The loss is genuine. The uniform configuration on $\mu_Q$ has $\det G=1$ (item 5 above), while the separation bound gives at most $(e/r)(4/Q)^{r-1}$.

*Proof.* Each nonzero term in Theorem 7.1 is at least $s^{r(r-1)}$, and $M_r\le\binom Nr\le(eN/r)^r$. ∎

*Exact obstruction for $\ln2$.* The BBP models $2^n\ln2\equiv s_n+T_n\pmod1$ (§5.5) have $s_n=A_n/Q_n$, where $Q_n$ contains every prime $p\in(\sqrt n,n]$ with $p\nmid A_{\lfloor n/p\rfloor}$ (Phase 23, `GF-35`). So $\log\operatorname{lcm}_{n<N}Q_n\sim N$ by the prime number theorem. Two consequences:

- **Separation route.** The budget is $r\log(e/(rc))$ against a cost of $r(r-1)\log(Q/4)\asymp r(r-1)N$. Only $r=1$ survives for large $N$.
- **Norm route.** Proposition 7.2(2) costs $\varphi(Q)\log N$ per dimension, which is astronomically larger.
- **Irrationality-measure route.** Separation from $\mu(\ln2)\le3.5746$ (Marcovecchio 2009) gives $s\ge2^{-N(\mu-1+\varepsilon)}$, which is the same order of cost.

Every arithmetic lower bound of this kind is therefore **void at $r=2$**, and $r=2$ is precisely the Weyl-sum problem of Theorem 6.2. The entire difficulty of $D^+(\ln2;2)<1$ sits in the 2×2 determinant
$$1-\lvert S_N(1)\rvert^2=N^{-2}\sum_{i<j}\lvert z_i-z_j\rvert^2,$$
and no amount of higher-dimensional amplification removes it, by Corollary 1.5(2) and Theorem 1.2.

### 7.4 Rank-only countermodel

**Theorem 7.4 (A7.4; Paper proof).** For **every** irrational $x$, every $h\ne0$ and every $r\le N$, every Cauchy–Binet term of $\det G_{N,r}(h)$ is strictly positive (Proposition 1.6). This includes
$$L_b=\sum_{k\ge1}b^{-k!}\in K_b .$$
For $L_b$, $C_b(L_b)=\{\delta_0\}$, so $\det G_{N,2}(1)\to0$, $(\det G_{N,r(N)})^{1/r(N)}\to0$ for every $r(N)\to\infty$, and $D_N\to1$. Hence **no argument using only rank, nonvanishing or distinctness** of the orbit points can give $a_*>0$ or $D^+<1$.

*Proof that $L_b\in K_b$.* If the next nonzero digit after position $n$ is at position $k!$, then $t_n<2b^{-(k!-n)}$. Positions within distance $d$ of the next $k!$ number at most $d$ per $k$, and there are $o(\log N)$ values of $k$ with $k!\le N$. So for every $d$, a density-one set of $n$ has $t_n<2b^{-d}$. ∎

Quantitative separation does not rescue rank-only arguments either. Witnesses with finite irrationality exponent exist at both extremes $D=0$ and $D=1$: `AC-11` (paired witnesses for its irrationality-exponent run-bound class), `GF-28` (the Kempner–Shallit badly approximable number in $K_2$: $\mu=2$, $D=1$), and `GF-33` and `GF-46` ($\mu=2$ and badly approximable normal numbers: $D=0$).

### 7.5 Denominator-only countermodel

**Theorem 7.5 (A7.4; Paper proof, Finite certificate).** Let $(Q_n)$ be any strictly increasing sequence of integers. Examples are the BBP denominators of $\ln2$ (after passing to a subsequence) or a sequence containing every prime. The configuration $z'_n=e(1/Q_n)$ has:

- reduced denominators exactly $Q_n$;
- pairwise distinct points;
- every Cauchy–Binet term positive.

Yet $\mu'_N\to\delta_0$, so $\det G'_{N,2}(1)=1-\lvert S'_N(1)\rvert^2\to0$, every growing-dimension root tends to $0$, and $D'_N\to1$. Consequently any lower bound on $\det G_{N,r}$, on $1-\lvert S_N(1)\rvert$, or on $1-D_N$ that depends only on the denominators, the rank and distinctness is at most its value for $z'$, which tends to $0$.

*Exact analogue in the script.* For the rational circle points $z(1/(K+n))$, $n<N=K\in\{4,8,12,16\}$:

- all points are distinct;
- every pairwise factor $\lvert z_i-z_j\rvert^2$ is positive;
- $\det G_{N,r}>0$ for $r\le3$;
- yet $\det G_{N,2}=N^{-2}\sum_{i<j}\lvert z_i-z_j\rvert^2<2/K^2$, exactly.

### 7.6 Large sieve and selected subsets

- **Large sieve.** The Montgomery–Vaughan form of the large sieve gives $\lambda_{\max}(G_{N,r})\le(r-1+\delta_N^{-1})/N$, where $\delta_N$ is the minimal separation. This is an **upper** spectral bound. Combined with $\operatorname{tr}G=r$ it gives
$$\lambda_{\min}\ge r-(r-1)\lambda_{\max},$$
  which is nontrivial only when $N\delta_N>1-O(1/r)$, i.e. for nearly perfectly spaced point sets (three-gap configurations). For i.i.d. uniform points $\delta_N\asymp N^{-2}$. No lower bound for $\times b$ orbits follows. (A genuine but presumably vacuous sufficient condition: if $N\delta_N\ge\kappa$ for all $N$ and some fixed $\kappa>0$, then every limit measure is at most $\lambda/\kappa$, so it is absolutely continuous and hence equal to $\lambda$, and $x$ is normal. Whether any $\times b$ orbit satisfies this is **Open**.)
- **Selected subsets.** $\det G_{N,r}=\frac{\binom Nr}{N^r}\cdot\operatorname{avg}_I\lvert V_I\rvert^2$, and for uniform points $\mathbb E\lvert V_I\rvert^2=r!$ (Theorem 5.7). A positive root therefore means that the average normalized Vandermonde energy $\lvert V_I\rvert^2/r!$ over $r$-subsets is at least about $c^r$. Restricting to structured subfamilies, such as near-regular $r$-gons with $\lvert V\rvert^2\approx r^r$, gives lower bounds only through counts of such configurations. That is an $r$-point correlation (equidistribution at scale $1/r$) statement, with no arithmetic shortcut.

---

## 8. Determinant-method requirements (the nine-point ledger)

| Requirement | Toeplitz orbit determinant $\det G_{N,r}(h)$ | Reference |
| --- | --- | --- |
| Rank | $\min(r,\#\{z_n\})$. For limits, $\operatorname{rank}T_m(\nu)=\min(m,\#\operatorname{supp}\nu)$ | Prop. 1.6, Thm. 6.3 |
| Nonvanishing | Automatic for every irrational $x$ and every $r\le N$, so it carries **no** distributional information | Thm. 7.4 |
| Prime-local valuations | Rational orbits with $Q=p$: $\mathfrak p^{r(r-1)}\mid N^r\det G$, attained by the uniform configuration. This controls only the conjugate-family mean | Prop. 7.2 |
| Denominator and height bounds | $N^r\det G$ is a totally nonnegative algebraic integer with house at most $N^r$. Liouville: $\det\ge N^{-r\varphi(Q)}$ | Prop. 7.2 |
| Analytic upper bounds | $(1-\lvert S\rvert^2)^{r-1}$; Burg $\prod_{k\le m}(1-\lvert\alpha_k\rvert^2)^{r-k}$; monotone root; Szegő limit $a(\mu)$; two-sided Fourier-energy estimate, valid only while $\lVert G-I\rVert<1$ (its unrestricted converse fails) | Thms. 1.2, 1.3, 5.3; Cor. 5.4; Prop. 2.4 |
| Approximation stability | $\lVert\Delta G\rVert\le\pi\lvert h\rvert r(r-1)\bar\varepsilon$; regularized log-root is $1/t$-Lipschitz; $\ln2$ BBP models are faithful for $r=o((N/\log N)^{1/2})$ | Lemma 5.6, Thm. 6.1 |
| Dimension dependence | $r\le N$. Normal $x$ with $D_N\le\varepsilon$: $r=o(1/\varepsilon)$. Optimal schedules depend on $x$, even for normal $x$, and cannot be computed uniformly from a program for $x$. $r=N$ fails for random points | Cor. 5.4, Props. 3.5–3.6, Thm. 5.7 |
| Amplification-cost accounting | Analytic side: the normalized root is a Cesàro mean of log-residuals, so **higher dimension never reveals more than the residual sequence** $d_j$. Arithmetic side: separation costs $r(r-1)\log(Q/4)$ and Liouville costs $r\varphi(Q)\log N$, against the net budget $r\log(e/(rc))$. For $\ln2$, $\log Q\sim N$, so only $r=1$ survives | Cor. 1.5, Prop. 7.3 |
| Adversarial countermodels | Rank-only $L_b$; denominator-only $e(1/Q_n)$; biased Bernoulli (all words positive, $D^+<1$, $a_*=0$); $\mu_\alpha$ (sharpness); primitive-root rationals ($\det\approx1$ at fixed $r$, $a_*=0$); de Bruijn normal numbers defeating any fixed schedule and any uniform schedule algorithm; compound-symmetric configurations with root $\to1$ but divergent Fejér energy; base-3 two-fixed-point law (the $h=b-1$ test is not necessary) | §3, §4, §5.3, §7 |

## 9. Determinant-method frontier (for the Track H4 table)

| Constant or family | Auxiliary object | Proven nonvanishing / divisibility | Analytic upper bound | Denominator cost | Existing obstruction | Remaining missing estimate | Evidence |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $\ln2$ (`BC-09`) | $G_{N,r}(1)$ of the orbit or of its BBP models | Full rank (irrational); models $\mathfrak p$-divisible for every large-prime band | $\det G_{N,2}=1-\lvert S_N(1)\rvert^2$; Thm. 6.2 thresholds $0.99979995$ and $1-16/(27\cdot10^{12})$ | $\log Q_N\sim N$; separation cost $\asymp r^2N$ | Prop. 7.3: only $r=1$ survives; GF-47 $O(\log N)$-reset barrier; Phase 23 saving is only $\log N/N$ | A **fixed** saving, e.g. $\limsup\lvert S_N(1)\rvert\le0.9997$ (any value $\le0.99979995$ suffices) | Open (exact reformulation: Paper proof) |
| Erdős–Borwein $E$ (`BC-37`), $E_+$ (`BC-39`) | $G_{N,2}(1)$ | Full rank | Thm. 6.2 | Lambert denominators | Column-correlation barriers (`GF-47`) | Fixed saving in $S_N(1)$, equivalent to $D^+<1$ | `BC-37`: external claim (`CC-20`/`CC-21`), not independently verified; `BC-39`: Open |
| Stoneham $\alpha(b,c)$ (`BC-49`, `ST-28`) | $G_{N,r}(h)$ | Full rank; complete Ramanujan cancellation on full shells | $\lVert G-I\rVert\le\pi\lvert h\rvert(r-1)CN^{-1/2}(1+\log N)^2$ | $c^k$ (power of a fixed prime) | None (normal) | Shell-aligned range $r\approx N/\log N$ (heuristic) | Paper proof (control from `ST-28`); range: Open |
| Champernowne (`BC-47`), localized logarithms (`LS-01`) | $G_{N,r}(h)$ | Full rank | Cor. 5.4 with the known discrepancy rates | n/a | None | Explicit $D_N$ rates give explicit schedules | Paper proof (control) |
| $E_b$, $E_b^3$ (`GF-03`, `GF-04`) | $G_{N,2}(1)$ | Full rank | $\det G_{N,2}(1)\to0$ | n/a | n/a | None: classified ($K_b$) | Paper proof (from GF-03/04) |
| Lambert values with $D^+<1$ (`GF-42`) | $G_{N,2}(1)$, $G_{N,m}(1)$ | $\liminf\det G_{N,2}(1)>0$ (**new corollary**) | Thm. 6.3 hierarchy | Lambert | $a_*$ unknown | Whether the limit measures carry Lebesgue mass; level-$m$ positivity for $m\ge3$ | Paper proof (corollary of GF-42 and Thm. 6.2) |
| `GF-45` reciprocals | $T_r(\mu_\alpha)=(1-\alpha)I+\alpha J$ | Exact | Root $\to1-\alpha$ | Reciprocal periods | — | None (Phase 26 Audit III passed) | External input `GF-45` (registered `Paper proof`; Audit III: 0 Critical, 0 Major; cross-model, not human peer review) |
| Synthetic: biased Bernoulli, Markov | $T_r(\mu)$ | $D_m>0$ for all $m$ | Root $\to0$ | n/a | — | — | Paper proof; Finite certificate |

---

## 10. Prior art, external inputs and hypothesis verification

**Prior art.**

- Toeplitz determinants and their limits: Szegő (1915, 1920); Kolmogorov (1941); Krein (1945); Verblunsky (1935–36); Grenander–Szegő (1958); Simon, *OPUC* (2005).
- Levinson–Durbin recursion and Burg's maximum-entropy extension (1967/1975).
- Multivariate prediction: Helson–Lowdenslager (1958).
- Equidistribution: Weyl (1916); Koksma (1942); Erdős–Turán (1948); Kuipers–Niederreiter, *Uniform Distribution of Sequences* (1974). The sharp constant $2$ in Theorem 5.1 is elementary; we found no explicit statement of its sharpness in the sources consulted and make **no priority claim**.
- Large sieve: Montgomery–Vaughan (1973) and Selberg.
- Normality and equidistribution of $\{b^nx\}$: Wall (1949). Borel hierarchy: Ki–Linton (1994).
- Invariant measures of $\times b$: the identity $a(\mu)=\mu(\mathcal N_b)$ (Proposition 2.7) is an elementary observation, presumably folklore.
- Repository lineage: Phase 23 Proposition 5.1 (`GF-35`) gives the binary qualitative form of Theorem 6.2, its 0.9997 threshold and the transition minorant. `GF-47` records the $O(\log N)$-reset barrier showing that BBP resets permit $S_N(1)\to1$, which is consistent with Theorem 6.2. `AC-10` and `AC-11` give rational-orbit and irrationality-exponent obstructions. `CC-50` gives the Legendre–Bezout window–denominator barrier for $\ln2$. `GF-28`, `GF-33` and `GF-46` give finite-irrationality-exponent witnesses at $D=1$ and $D=0$ (§7.4).

To our knowledge, the following are new as stated, though each is elementary given its inputs:

- the orbit-vector proof of the Verblunsky factorization;
- the optimal-rate characterization $a_*$ and its strict separation from $D^+<1$;
- the no-universal-schedule theorem;
- the linear-in-$r$ Toeplitz bound;
- the random-point law;
- the separation-cost barrier.

A specialist literature search (Track G) should confirm or refute this before any priority claim.

**External inputs and hypothesis checks.**

| Input | Where used | Hypotheses checked |
| --- | --- | --- |
| Lebesgue decomposition, Riesz/weak-$*$ compactness, Portmanteau, Pólya, Fourier uniqueness, Riemann–Lebesgue, smooth Urysohn, inner/outer regularity | §2–§3 | Standard. Measures on the compact metric space $\mathbb{T}$ |
| Szegő–Kolmogorov–Krein (Theorem S) | Prop. 1.8(5) only | Any finite positive Borel measure. Not needed for A2/A3/A6, which use Prop. 2.4 |
| Helson–Lowdenslager | Prop. 1.7(3) only | Lexicographic half-space. Box approximation **not verified** (labelled External input) |
| Borel's normal number theorem | Prop. 2.7, 3.2 | $\lambda(\mathcal N_b)=1$ |
| Birkhoff's ergodic theorem | Prop. 3.2 | $\mu_p$ ergodic for $T_2$ |
| Champernowne normality in base $b$ | Prop. 4.3 | Classical for every $b\ge2$ |
| `ST-28` (Vandehey Thm. 5.1 and Erdős–Turán) | Cor. 5.5 | Coprime $b,c$, $c>2$, degree one: $(\eta,\ell)=(1/2,2)$ |
| `GF-45` | Thm. 4.2(1)–(2) (arithmetic witnesses) | One witness per $(b,\alpha)$. Registered `Paper proof`; Phase 26 Audit III passed (0 Critical, 0 Major; cross-model, not human peer review). Used as an external input, not reproved here |
| `GF-03`, `GF-04`, `GF-42` | Control table | As registered. The signed-family range of `GF-42` follows the Stage 0 correction ($k\ge k_0$) |
| Ki–Linton (1994) | Prop. 3.4(2) | $\Pi^0_3$-completeness of $\mathcal N_b$ in the Borel hierarchy, for every $b\ge2$ |
| `AC-11` | Prop. 3.4(3) | Non-computable, non-c.e. and non-co-c.e. recognition of normality for digit-oracle codes. Kernel-verified for $b=2$ with the endpoint properties as inputs; the transfer to $b\ge2$ is a paper deduction. Not used in Prop. 3.6 |
| Kleene's recursion theorem; s-m-n theorem | Prop. 3.6 | Standard; any acceptable numbering of the partial computable functions |
| Marcovecchio (2009), $\mu(\ln2)\le3.5746$ | §6.2, §7.3 | As used in Phase 23 |
| Prime number theorem ($\log\operatorname{lcm}(1..n)\sim n$) | §7.3 | Standard |

---

## 11. Reproduction and verification record

```text
python -B scripts/phase26_toeplitz_uniformity.py      # Windows, Python 3.13, exit code 0, about 7 s
```

| Script section | `[exact]` assertions | Content |
| --- | ---: | --- |
| A1 Gram determinant inequalities | 5,230 | 75 configurations over $\mathbb{Q}(i)$: A1.1, Gram–Schmidt factorization, Verblunsky recursion via projections, Burg bounds, monotone root, Fischer with remainder, equality iff geometric, rank; 35 geometric Toeplitz identities |
| A4 exact controls | 1,747 | $(1-\alpha)I+\alpha J$ for 10 values of $\alpha$ and $r\le12$; eigenvectors; root sandwich; regularization; primitive-root orbits in $\mathbb{Z}[\zeta_Q]$; periodic-orbit ranks |
| A5 Koksma constant and Toeplitz norms | 31,642 | 1,702 grid configurations × 6 harmonics; sharpness certificate with outward-rounded $\mathrm{Re}\,S_N(1)\ge0.101781$, $\lvert h\rvert D_N=0.052$ and ratio $>1.957$ asserted exactly; 1,125 Sylvester certificates of $\lVert G-I\rVert<3.14159\lvert h\rvert(r-1)D_N$; Frobenius identities; the Corollary 5.4 counterexample $G_{N,r}(1)=(1-\alpha)I+\alpha J$ with $r=m^4$, $\alpha=\frac1{2m}$ for $2\le m\le6$, with Weyl sums checked in $\mathbb{Z}[\zeta_{N-K}]$ and the $r\times r$ determinant by elimination for $m\le3$ |
| A6 weak positivity certificates | 16,234 | $\ln2$ thresholds; 6,256 per-$N$ inequalities linking $D_N$ and $\lvert S_N(1)\rvert$; Bernoulli bounds and the outward-rounded enclosure $D(\mu_{1/3})\in[0.239065,0.247017]$, asserted exactly; 504 interval-mass certificates |
| A7 Cauchy–Binet and countermodels | 22,199 | Cauchy–Binet over $\mathbb{Q}(i)$ and $\mathbb{Z}[\zeta_Q]$; norms and Vandermonde divisibility; uniform-roots identity ($Q\le9$); random-point law on $\mu_4$ ($N\le6$); clustered countermodel |
| **Total `[exact]`** | **77,052** | |
| `[finite]` floating point | 198 | §12. Isolated; not used in any proof |

No A7 check was removed. The A7 count is 16 lower than before the post-review repair only because the cached `cyclotomic()` construction checks for some small $\Phi_d$ are now first triggered by the counterexample check in A5. Diagnostic decimals printed by the exact sections are outward-rounded by integer arithmetic; an AST scan finds no float literal, `float()` call or `math`/`cmath` use outside the `[finite]` section.

**Revision record (post-review repair).** The note and the script were revised after the cross-provider review [`reviews/track-a-review.md`](reviews/track-a-review.md), whose verdict was REVISE (0 Critical, 2 Major, 9 Minor).

- MJ-1: the converse of Corollary 5.4 is restricted to $\limsup\lVert G-I\rVert<1$ and to sub-dimensions, with an explicit counterexample, an exact certificate and an orbit realization.
- MJ-2: Proposition 3.4(3) no longer infers the absence of uniform schedules from `AC-11`. Proposition 3.6 proves it with Kleene's recursion theorem, and row A3.4 now matches Proposition 3.4(2) and §10.
- MN-1 to MN-9 are repaired in place.

Cross-model review is not independent human peer review.

---

## 12. Finite measurements (`[finite]`; finite data only, never evidence for asymptotics)

The table lists $(\det G_{N,r}(1))^{1/r}$ for orbit points taken from 53-bit windows of exactly computed binary expansions. The Bernoulli sequence is pseudo-random with a fixed seed. "$\mu_{1/2}$" is the construction of Proposition 4.3 with $\alpha=\frac12$.

| Number | $N$ | $\lvert S_N(1)\rvert$ | $r=2$ | $r=4$ | $r=8$ | $r=16$ | $r=32$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $\ln2$ | 4096 | 0.02478 | 0.99969 | 0.99908 | 0.99813 | 0.99651 | 0.99365 |
| Stoneham $\alpha(2,3)$ | 4096 | 0.00707 | 0.99997 | 0.99994 | 0.99989 | 0.99981 | 0.99965 |
| Champernowne (base 2) | 4096 | 0.08156 | 0.99667 | 0.99144 | 0.98487 | 0.97730 | 0.96891 |
| Euler $E_2$ | 4096 | 0.91470 | 0.40413 | 0.22500 | 0.10075 | 0.03521 | 0.00306 |
| Bernoulli $p=\frac13$ | 4096 | 0.22278 | 0.97487 | 0.93762 | 0.89637 | 0.85440 | 0.80913 |
| $\mu_{1/2}$ construction | 4096 | 0.47368 | 0.88069 | 0.77496 | 0.69638 | 0.64244 | 0.60527 |

These numbers **illustrate the finite-scale illusion**. For biased Bernoulli the true asymptotic root is $0$ (Proposition 3.2), but at $r=32$ the measured root is still $0.81$. This is consistent with a slow decay of $d_j(\mu_{1/3})$, as expected since $\dim\mu_{1/3}=h(\frac13)/\log2\approx0.918$ is close to $1$. Fixed-dimension and small-$r$ data cannot distinguish a Lebesgue component from a singular measure of high dimension. The $\ln2$ row is a finite measurement only, and it says nothing about $D^+(\ln2;2)$.

---

## 13. Explicit open questions

1. **Finite-$N$ determinant-to-mass transfer.** Does $\det G_{N,r}(h)^{1/r}\ge c$ at a **single** finite $N$, with $r$ large, imply an explicit interval-mass lower bound at the same $N$, through Gram–Schmidt residuals $d_m\ge c^{r/(r-m)}$ and Christoffel functions? Theorem 6.4 does this with $\lambda_{\min}$.
2. **Shell-aligned Stoneham range.** Prove $\lVert G_{N,r}-I\rVert\lesssim r\log N/N$ at shell-aligned $N$ (§5.4).
3. **Dimension window for random and normal points.** Determine the threshold $r(N)$, between $(N/\log\log N)^{1/2}$ and $N$, at which $\det G_{N,r}^{1/r}\to1$ fails almost surely.
4. **Multilevel Szegő with singular parts on boxes.** Complete Proposition 1.7(3) with full details. Is the joint determinant of $(\{b^nx\},\{b^nx^2\})$ informative for any explicit $x$?
5. **Time-shift determinants and $D^+<1$.** Characterize $\lim_r(\det H_r)^{1/r}$ (Proposition 1.8) for the Lambert families of `GF-42`, and decide whether a positive time-shift rate can be **proved** for any constant whose normality is open.
6. **Lebesgue component for proved $D^+<1$ families.** For any family with $0<D^-\le D^+<1$ (`GF-42`), decide whether $a_*>0$.
7. **Level-3 positivity.** For $\ln2$, or for $E$ (`BC-37`), is there any arithmetic route to $\liminf\det G_{N,m}(1)>0$ for **some** fixed $m$? By Theorem 6.3 this is equivalent to excluding limit measures with fewer than $m$ atoms. $m=2$ is exactly $D^+<1$.
8. **Near-perfect spacing.** Is $N\delta_N\ge\kappa>0$ ever possible for a $\times b$ orbit (§7.6)?

## 14. Standing research objectives advanced

- **Objective 1 (normality).** Theorem 2.1 with $c=1$ is a new sufficient criterion for normality. Theorem 3.1 shows it is also necessary for some schedule. Corollaries 5.4–5.5 give quantitative determinant rates for normal Stoneham numbers. These are controls deduced from known normality.
- **Objective 2 (nonnormality).** Lemma 2.6 and Theorem 6.2 characterize $K_b$ by $\lvert S_N(1)\rvert\to1$ and by fixed-point Diracs in every radix. No new nonnormality theorem for a classical constant is claimed.
- **Objective 3 (quantification).**
  - Exact characterization of the determinant rate as $a_*=\inf_\mu\mu(\mathcal N_b)$.
  - Sharp $D^+\le1-c$.
  - Exact Koksma constant $2$.
  - Linear-in-$r$ Toeplitz bound.
  - Explicit two-sided constants linking $D^+$ and $\limsup\lvert S_N(1)\rvert$.
  - New corollary: $\liminf\det G_{N,2}(1)>0$ for every `GF-42` family with $D^+<1$.
  - Exact enclosure of $D(\mu_{1/3})$.
- **Objective 4 (limitations).**
  - Regularization adds no information (Theorem 6.1).
  - Positive word frequencies do not imply a Lebesgue component (Proposition 3.2).
  - No universal schedule exists (Proposition 3.5), and optimal schedules are non-effective: no algorithm computes them uniformly from a program for $x$ (Propositions 3.4 and 3.6).
  - Outside the regime $\lVert G-I\rVert<1$ the determinant root does not control the Fejér energy at the full dimension (Corollary 5.4).
  - Separation-cost barrier, with only $r=1$ surviving for $\ln2$ (Proposition 7.3).
  - Rank-only and denominator-only countermodels (Theorems 7.4 and 7.5).
  - Galois averaging controls only the conjugate-family mean (Proposition 7.2).

## 15. Determinant-programme assessment (Track A contribution)

1. **Which mechanisms work?**
   - Growing-dimension Toeplitz roots measure exactly the Lebesgue component $a_*$ (Theorem 3.1).
   - Fixed-dimension determinants measure exclusion of finitely supported limits; level 2 is exactly $D^+<1$ (Theorems 6.2 and 6.3).
   - Time-shift determinants measure linear unpredictability (Proposition 1.8).
   - All of these are exact and proved. None produces a new theorem for a classical constant by itself.
2. **Which are only equivalent reformulations?**
   - Polynomial combinations and other single frequencies $h$.
   - Regularization: an affine image of $a_*$.
   - The 2×2 criterion for $D^+<1$, which is a reformulation of the Weyl-sum problem.
   - Determinant amplification in $r$, which never exceeds the residual sequence.
3. **Arithmetic lower bounds established.** Total nonnegativity, Vandermonde divisibility $p^{r(r-1)}\mid\mathrm{Norm}$, and the Liouville bound $N^{-r\varphi(Q)}$ for rational orbits (Proposition 7.2). All are averaged over the conjugate family.
4. **Analytic upper bounds established.** Theorems 1.2, 1.3, 5.1–5.3; Proposition 2.4; Corollary 1.4.
5. **Exact remaining incompatibility for $\ln2$.** The arithmetic budget supports only $r=1$, while the needed statement is a fixed saving $\limsup\lvert S_N(1)\rvert\le0.99979995$. The known saving is $\log N/N$. The loss is a factor of order $N/\log N$ in the 2×2 determinant, i.e. in $1-\lvert S_N(1)\rvert^2$.
6. **Countermodels that survive.** Rank-only ($L_b$), denominator-only ($e(1/Q_n)$), biased Bernoulli, primitive-root rationals, de Bruijn normal numbers (against fixed schedules and against uniform schedule algorithms), the compound-symmetric Fejér-energy countermodel of Corollary 5.4, and the GF-47 reset model.
7. **Transfer to other constants.** Theorems 2.1, 3.1, 6.2, 6.3 and 6.4 are universal, valid for every $x$ and $b$. The Stoneham control transfers to every family with a power-saving discrepancy (`ST-28` polynomial images, `LS-01`). The ln 2 barrier of §7.3 transfers verbatim to every BBP-type constant whose model denominators satisfy $\log Q_N\ge cN$ for some constant $c>0$: $\ln3$, $\ln10$, $\pi$ and $\zeta(3)$ models.

*Cross-model review of this note is not independent human peer review. No benchmark status changes.*
