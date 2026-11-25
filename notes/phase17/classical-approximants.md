# Classical constants and usable rational approximants: correlated rounding, the grid ceiling and the window–denominator barrier

**Verdict, read first.**

1. **Nothing here advances an asymptotic digit-distribution statement** for $\ln 2$, $\pi$, $e$, $\sqrt2$ or $\varphi$. $D^+(\ln 2)<1$, $D^+(\varphi)<1$ and every analogue remain exactly as open as before. The rigorous digit statistics are still $\gg\sqrt N$ ones (quadratics) and $\gg(\log N)^{3/2}$ digit changes (general algebraic irrationals), against an observed $N/2$.
2. **What is genuinely new and proved (small, constructive, and unable to reach digits).** Correlated (Bezout) rounding removes the Phase 16 two-adic shift entirely ($w=0$, $q_N\mid L_D$). Together with the **Legendre** kernel, instead of the first-kind Chebyshev kernel, it gives a *linear* window $T_N=\log_2L_D-O(1)\approx N/\ln\rho_{\min}$ at denominator rate $\ln2/\ln\rho_{\min}$ (Theorem 3). This closes the "linear window of consecutive shifts" boundary recorded at the end of Phase 16, **in the weak sense of window length**.
3. **What is negative and sharp (the real content of the track).**
   * The first-kind Chebyshev kernel has an analytic floor $|E_D|\asymp D^{-2}$ (Theorem 2). For it, correlated rounding cannot give a window beyond $2\log_2D+O(1)$. The brief's claim "$w=0$ **and** $T_N\sim D/\ln2$" is false for $T_D$ and true only for the Legendre kernel.
   * The correlated Legendre numerator **is** the $\ln2$-aware nearest-grid numerator $\operatorname{round}(L_D2^N\ln2)$ (Proposition 4; checked exactly on all 10 Legendre–Bezout rows). "$\ln2$-free" describes the algorithm, not the number it outputs. The numerator carries no arithmetic beyond the digits of $\ln2$ themselves.
   * **Window–denominator barrier (Theorem 6, unconditional given $\mu(\ln2)<\infty$).** Every rational approximant has $T_N\le(\mu-1)N+\mu\log_2q_N+O(1)$. Any family with positive denominator rate therefore has $T_N\le C\log_2q_N$ and cannot satisfy the incomplete-orbit hypothesis $T_N\ge q_N^\delta$. This holds for *every* method, any dimension and any height. The Chebyshev-pole families fail twice: their prime support grows, whereas Vandehey's estimate (as used in Phase 13) needs a fixed finite support $S$.
   * **E3.** Dimension and height cannot beat the grid. All $\theta$ in a cancellation coset share one ceiling $T\le\log_2q^*+\log_2(1/\eta^*)$ (Theorem 7(b), verified exactly). The Minkowski trade-off $(k_{\rm eff}-1)\ln H=\ln M_{\rm eff}+T\ln2+O(1)$ holds below that ceiling and saturates at it. Exactly vanishing bands cost no height but remove one dimension each, which the per-prime index count of Phase 16 §7 misses.
4. **Citation corrections to the brief** (verified by search, §8.3). The $N^{1/D}$ count of 1-bits is Bailey–Borwein–Crandall–Pomerance (2004), not Bailey–Crandall (2002). Bugeaud (2007) and Bugeaud–Evertse (2008) give *polylogarithmic* lower bounds for digit changes, not $\sqrt N$. Davis (1978, 1979) proved **both** matching upper and lower bounds with sharp constant $1/2$ for $|e - p/q| \asymp \frac{\log\log q}{q^2\log q}$ via Euler's continued fraction.

Scope: paper proofs plus exact finite computations in [phase17_classical_approximants.py](../../scripts/phase17_classical_approximants.py). No Lean files were added or changed in this track.

## 0. Status

| Result | Status | Evidence |
| --- | --- | --- |
| Thm 1: Bezout correlated rounding, $q_N\mid L_D$, $w=0$ | Paper proof (elementary) | Asserted on 40 rows: $\sum\delta_km_k=\Delta$, $\lvert\int Q-S\rvert\le1/(2L_D)$, $q\mid L_D$, support $\subset\{p\le D\}$ |
| Thm 2(a): Chebyshev analytic floor $E_D\sim cD^{-2}$ | Paper proof (two integrations by parts) | $E_D/\text{pred}=1.0000$–$1.0028$ for $D=40..320$, three pole families |
| Thm 2(b): Legendre remainder $\ll\rho_{\min}^{-D}$ | Classical Laplace integrals; exact numerics | $\log_2E_D=-105.4,-207.8,-411.7,-819.5$ at $D=40,80,160,320$ |
| Thm 3: $w=0$, $T_N=\log_2L_D-O(1)$, all $N$ | Paper proof + exact rows | $T=337$ ($D=240$, $N=605$) against Phase 16's $T=6$ |
| Prop 4: correlated Legendre numerator $=$ nearest-grid numerator | Paper proof + exact | Equal on all 10 Legendre–Bezout rows; differs on all 10 Chebyshev–Bezout rows |
| Thm 5: grid ceiling $T\le\log_2q+\log_2(1/\eta)$ | Rigorous, elementary | Exact assertion on every row and every adaptive $\theta$ |
| Thm 6: window–denominator barrier | Rigorous given $\mu(\ln2)<\infty$ | Constants $8.1$–$12.7$; $\delta_N$ table |
| Thm 7(a),(b): band accounting, coset ceiling | Rigorous | Verified for $k=1..4$ at $N=120$; $T^*=59.3,59.3,59.3,232.5$ |
| Thm 7(c): Minkowski law | Homogeneous Minkowski rigorous; threshold law heuristic | Slopes $0.669/0.693$, $0.355/0.347$, $0.326/0.347$ |
| E4 comparisons | Exact finite computation + literature | 32768-bit expansions, CF, Zeckendorf $n<600$, prefix denominators |

## 1. Setup

Pole data and notation are those of [Phase 16 §3.2](../phase16/nonflat-approximants.md): $\ln2=\sum_ic_i\int_0^1\frac{dx}{a_i-\sigma_ix}$, a polynomial kernel $K$ of degree $D$, $x_i=\sigma_ia_i$, and $K(x)-K(x_i)=(a_i-\sigma_ix)P_i(x)$. Put

```math
R_{\rm tot}=\sum_i\frac{c_i}{K(x_i)}P_i,\qquad e=\lfloor\log_2\min_i|K(x_i)|\rfloor,\qquad r_k=2^e[x^k]R_{\rm tot},\qquad S=\sum_{k<D}\frac{r_k}{k+1}.
```

The exact identity $\ln2=-\int_0^1R_{\rm tot}+I_D$, with $I_D=\sum_i\frac{c_i}{K(x_i)}\int_0^1\frac{K(x)}{a_i-\sigma_ix}dx$, gives

```math
2^e\ln2+S=E_D:=2^eI_D \qquad(\text{the analytic remainder}).
```

Write $L=L_D=\operatorname{lcm}(1,\dots,D)$ and $\rho_i=|z_i|+\sqrt{z_i^2-1}$ with $z_i=2a_i-\sigma_i$. Then $\rho_{\min}\ge3+2\sqrt2$ for every admissible pole set. Two kernels are used: **Chebyshev** $T_D(2x-1)$ (Phase 16) and **Legendre** $P_D(2x-1)=\sum_k(-1)^{D+k}\binom Dk\binom{D+k}kx^k\in\mathbb Z[x]$. For a polynomial $Q\in\mathbb Z[x]$ of degree $<D$ put $Y_N=-2^{-w}\int_0^1Q$ with $N=e-w$.

**Window convention.** $T_N=\lfloor-\log_2|2^N\ln2-Y_N|\rfloor-8$. This is the number of consecutive shifts $j$ for which $2^jY_N$ tracks $2^{N+j}\ln2$ within $2^{-8}$, the convention of Phase 16. $\log_2$ of the error is certified from an exact enclosure of $2^{4400}\ln2$ of width $<4401$ units.

## 2. Correlated rounding

**Theorem 1 (Bezout correlated rounding).** Let $m_k=L/(k+1)$ for $0\le k<D$, let $r_k\in\mathbb Q$ and $S=\sum r_k/(k+1)$. For each prime $p\le D$ let $P_p$ be the largest power of $p$ that is $\le D$. Put $n^*=\operatorname{round}(LS)$ and $\Delta=n^*-\sum_k\operatorname{round}(r_k)m_k$. Let $s_p\in(-P_p/2,P_p/2]$ with $s_p\equiv\Delta(L/P_p)^{-1}\pmod{P_p}$, and set $\delta_{P_p-1}=s_p$, $\delta_0=(\Delta-\sum_ps_pL/P_p)/L$, all other $\delta_k=0$. Then:

1. $\delta\in\mathbb Z^D$ and $\sum_k\delta_km_k=\Delta$.
2. $Q_k=\operatorname{round}(r_k)+\delta_k$ satisfies $\int_0^1Q=n^*/L$ and $|\int_0^1Q-S|\le1/(2L)$.
3. $|\delta_{P_p-1}|\le P_p/2\le D/2$ and $|\delta_0|\le H_D/2+\pi(D)/2+1$.
4. $\gcd_k(m_k)=1$. The grid $\frac1L\mathbb Z$ is exactly what integer polynomials of degree $<D$ can reach.

*Proof.* (1) The index $k=P_p-1$ has weight $L/P_p$, a unit modulo $p$. For $p'\ne p$, $P_p\mid L/P_{p'}$. Hence $\Delta-\sum_{p'}s_{p'}L/P_{p'}\equiv\Delta-s_pL/P_p\equiv0\pmod{P_p}$ for every $p$, so it is divisible by $\prod P_p=L$. (2) is immediate. (3) $|\Delta|\le\frac L2H_D+\frac12$ and $\sum_p|s_p|L/P_p\le L\pi(D)/2$. (4) For $p\le D$, $v_p(m_{P_p-1})=0$; primes $>D$ do not divide $L$. $\square$

The proof uses only the rational numbers $r_k$, never $\ln2$. For the exact grid claim, the image of $Q\mapsto\int Q$ is $\sum_k\mathbb Zm_k/L=\frac1L\mathbb Z$ by (4). Cost: polynomial time. The coefficient height is $\max|Q_k|\approx\max|r_k|$ (about $e$ bits) plus the corrections $\delta$, which stay below $D/2$ (measured $\max|\delta|=89$ and $101$ at $D=240$).

## 3. The kernel dichotomy: the analytic floor

**Theorem 2.** (a) *Chebyshev kernel.* Let $i^*$ be the pole minimising $|T_D(z_i)|$; it is unique in all three families. Put $g(u)=1/(z-\sigma u)$ with $z=2a_{i^*}-\sigma_{i^*}$. Then

```math
E_D=-\frac{c_{i^*}\,2^e}{T_D(\sigma_{i^*} z)}\cdot\frac{g(1)+(-1)^Dg(-1)}{D^2}\,\bigl(1+O(D^{-2})\bigr),
\qquad g(1)+(-1)^Dg(-1)\ne0 .
```

For the single pole $g(1)+(-1)^Dg(-1)=\tfrac14+(-1)^D\tfrac12$. Hence $|E_D|\asymp D^{-2}$. Any $Q$ with $|\int Q-S|\le D^{-3}$ (in particular the unrounded $S$ itself) has $|2^e\ln2+\int Q|\ge|E_D|-D^{-3}$.

(b) *Legendre kernel.* $|E_D|\le C\rho_{\min}^{-D}$.

*Proof.* (a) With $u=\cos\theta$, $\int_{-1}^1T_D(u)g(u)du=\int_0^\pi\cos(D\theta)h(\theta)d\theta$, $h=g(\cos\theta)\sin\theta$. Two integrations by parts, with $\sin(D\theta)=0$ at $0,\pi$, give $\frac1{D^2}[\cos(D\theta)h']_0^\pi-\frac1{D^2}\int\cos(D\theta)h''$, with $h'(0)=g(1)$ and $h'(\pi)=-g(-1)$. A further two integrations show the second term is $O(D^{-4})$. Other poles are smaller by $(\rho_{\min}/\rho_j)^D$. (b) By Neumann's formula $\int_{-1}^1\frac{P_D(u)}{z\mp u}du=(\pm1)^D2Q_D(z)$. For $z>1$, $Q_D(z)\ll D^{-1/2}\rho^{-D-1}$ and $P_D(z)\gg D^{-1/2}\rho^D$ (Laplace integrals). So each pole contributes $\ll2^e\rho_i^{-2D}\ll\rho_{\min}^{-D}$. $\square$

*Exact check* (script §1a). $E_D/\text{pred}$ equals $1.0011,1.0028,1.0003,1.0007,1.0001,1.0002,1.0000$ for the single pole at $D=40,41,80,81,160,161,320$. It equals $1.00004$–$1.00016$ for the two-stride and telescoping families at $D=160,161$. For Legendre, $\log_2E_D=-105.4,-207.8,-411.7,-819.5$ against $-D\log_2\rho=-101.7,-203.5,-406.9,-813.8$, and always $E_D<1/(2L_D)$ (e.g. $2^{-819}$ against $2^{-466}$ at $D=320$).

**Consequence.** For the Chebyshev kernel no $\ln2$-free procedure can have a window beyond $2\log_2D+O(1)$. To cancel $E_D$ one must know $2^e\ln2$ to $D^{-2}$, which is what $\ln2$-freeness forbids. The Legendre kernel has $E_D\ll\rho^{-D}$ with $\ln\rho_{\min}\ge1.763>1=\ln$ of the growth of $L_D$. Its remainder sits far *below* the grid spacing $1/L_D$, so the grid is the only error.

## 4. Linear windows from the Legendre kernel, and what they are

**Theorem 3 (Legendre–Bezout approximants).** For any pole decomposition and every $D$ with $\rho_{\min}^D\gg L_D$ (all $D\ge D_0$), let $Q$ be the Bezout rounding of $r$ from the Legendre kernel, $N=e$ and $Y_N=-\int Q\in\frac1{L_D}\mathbb Z$. Then:

1. $q_N\mid L_D$, $v_2(q_N)\le\lfloor\log_2D\rfloor$, and the prime support lies in $\{p\le D\}$ (here $w=0$).
2. $|2^N\ln2-Y_N|\le\frac1{2L_D}+C\rho_{\min}^{-D}$, hence $T_N\ge\log_2L_D-O(1)=(1+o(1))D/\ln2$.
3. Multiplying by $2^j$ with $0\le j<e(D+1)-e(D)\le\log_2\rho_{\min}+1$ moves $N=e(D)$ to $N=e(D)+j$ at a cost of $j=O(1)$ bits of window and no new denominator. So **every** large $N$ is covered, with $\limsup\frac{\log q_N}N\le\frac{\ln2}{\ln\rho_{\min}}$ and $\liminf\frac{T_N}N\ge\frac1{\ln\rho_{\min}}$. The three limits are $0.393$, $0.263$ and $\to0$ for the rate; $0.567$, $0.380$ and $1/\ln\bigl(2M+1+2\sqrt{M(M+1)}\bigr)$ for the window ($M=8$: $0.284$).

*Proof.* Theorems 1 and 2(b). $\square$

**Certified table** (script §1b; exact; $T$ and $T_{\rm grid}$ in bits; $\log_2\eta=\log_2\|2^wL_D2^N\ln2\|$; "Q-bits/$\delta$" is $\log_2\max|Q_k|$ and $\max|\delta_k|$; supp is the number of primes dividing $q_N$ out of the primes $\le D$).

| family, kernel, method | $D$ | $N$ | $w$ | $\log q_N/N$ | odd/$N$ | $v_2$ | supp | Q-bits / $\delta$ | $\log_2$ err | $T_N$ | $\log_2\eta$ | $T_{\rm grid}$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| single, Cheb, independent (Phase 16) | 240 | 596 | 13 | 0.4053 | 0.3832 | 19 | 51/52 | 609 / 0 | −14.89 | 6 | −1.5 | 350 |
| single, Cheb, Bezout | 240 | 609 | 0 | 0.3890 | 0.3822 | 6 | 52/52 | 610 / 89 | −16.57 | **8** | −1.5 | 337 |
| single, Legendre, independent | 240 | 592 | 13 | 0.4102 | 0.3879 | 19 | 52/52 | 605 / 0 | −14.61 | 6 | −1.1 | 350 |
| single, Legendre, Bezout | 240 | 605 | 0 | 0.3759 | 0.3679 | 7 | 50/52 | 605 / 101 | −345.42 | **337** | −1.1 | 337 |
| single, Legendre, Bezout | 120 | 300 | 0 | 0.3876 | 0.3738 | 6 | 30/30 | 300 / 49 | −171.43 | 163 | −2.1 | 163 |
| two-stride, Cheb, Bezout | 120 | 454 | 0 | 0.2586 | 0.2494 | 6 | 30/30 | 454 / 51 | −15.58 | 7 | −1.6 | 162 |
| two-stride, Legendre, Bezout | 120 | 451 | 0 | 0.2502 | 0.2410 | 6 | 29/30 | 451 / 48 | −170.48 | 162 | −1.1 | 162 |
| $M=8$, Cheb, independent | 120 | 597 | 12 | 0.1970 | 0.1761 | 18 | 28/30 | 609 / 0 | −14.05 | 6 | −1.6 | 174 |
| $M=8$, Cheb, Bezout | 120 | 609 | 0 | 0.1781 | 0.1736 | 4 | 29/30 | 609 / 49 | −17.24 | 9 | −1.6 | 162 |
| $M=8$, Legendre, Bezout | 120 | 606 | 0 | 0.1937 | 0.1868 | 6 | 30/30 | 606 / 43 | −172.92 | 164 | −3.6 | 164 |

Reading the table. Correlated rounding saves the two-adic shift ($v_2$ from 19 to 6 or 7) but, for Chebyshev, does not move $T$ off $2\log_2D\approx16$: the floor of Theorem 2(a). With the Legendre kernel the window rises from $6$ to $337$ at the same $N\approx600$, and equals the $\ln2$-aware nearest-grid window $T_{\rm grid}$ in every Legendre–Bezout row. At $D=240$, $N/D=2.5208<\log_2\rho=2.5431$ puts the unreduced grid rate $\ln L_{240}/N=0.3946$ slightly *above* the asymptotic limit $0.3932$; the reduced rate drops to $0.3759$ because of accidental gcd cancellation $\gcd(n^*,L_{240})>1$ ($\log_2 q=328.1$ versus $\log_2 L_{240}=344.4$, with $50$ of $52$ primes surviving).

**Proposition 4 (identification).** If $L_D|E_D|<\operatorname{dist}(L_D2^N\ln2,\ \mathbb Z+\tfrac12)$, then the correlated numerator satisfies $-n^*=\operatorname{round}(L_D2^N\ln2)$ exactly. By Theorem 2(b), $L_D|E_D|\le2^{-(\log_2\rho_{\min}-1/\ln2)D}$, so exceptional $D$ have exponentially small measure in the target (finitely many for Lebesgue-a.e. real by Borel–Cantelli, and heuristically rare for $\ln2$). *Proof.* $LS=-L2^e\ln2+LE_D$, and rounding is stable under a perturbation smaller than the distance to a half-integer. $\square$ The script asserts equality of the two integers for all 10 Legendre–Bezout rows. It fails (as it must) for all Chebyshev–Bezout rows.

**Corollary (circularity).** The numerator of the Legendre–Bezout approximant is $\operatorname{round}(L_D2^N\ln2)$. Its residues modulo the primes $p\mid L_D$ are exactly as unstructured as the digits of $\ln2$. The construction therefore cannot give an independent arithmetic handle on those digits. This is a precise form of "no progress": the Phase 14–15 formulas had numerators with Frobenius structure; rounded approximants do not.

## 5. The nearest-grid benchmark and the ceiling

**Theorem 5 (grid ceiling).** If $Y\in\frac1q\mathbb Z$ then $|2^N\ln2-Y|\ge\|q2^N\ln2\|/q$, with equality iff $qY$ is the nearest integer. Hence

```math
T(Y)\le\log_2q+\log_2\frac1{\eta_{N,q}},\qquad\eta_{N,q}=\|q2^N\ln2\| .
```

*Proof.* $|2^N\ln2-a/q|=|q2^N\ln2-a|/q$. $\square$ The script asserts the inequality exactly on every row, and on every adaptive $\theta$ of E3. Correlated rounding attains equality up to the $O(1)$ of $E_D$ and ties, so $T=\log_2L_D+\log_2(1/\eta_{N,L_D})+O(1)$, i.e. $L_D\cdot\text{error}\sim\eta$.

**Why a factor $(1+c)$ is not available by any method here.** $T\ge(1+c)\log_2L_D$ is equivalent to $\eta_{N,L_D}\le L_D^{-c}$, a Diophantine coincidence for the *prescribed* multiplier $L_D2^N$. Dirichlet's pigeonhole guarantees a good multiplier among $M$ candidates, with $\|mx\|\le1/M$, but gives no control on which. Forcing one prescribed multiplier needs about $L_D^c$ trials, $e^{cD}$, exponentially many in $D\approx N/\log_2\rho$. The construction offers $\operatorname{poly}(D)$ trials (poles, the $O(1)$ shifts, $D$ itself). Exact experiment (script §1d): over 3000 consecutive $N$ with $L=L_{240}$ ($\log_2L=344.4$), the proportion with $\eta\le2^{-j}$ is $0.2503,0.0617,0.0057,0.0023$ for $j=3,5,8,10$, against the uniform model $0.25,0.0625,0.0078,0.0020$. The best gain is $13.3$ bits from $3000$ trials ($\log_23000=11.6$). A gain of $c\log_2L=34$ bits ($c=1/10$) would need about $2^{34}$ trials.

What is and is not proved:

* Unconditional: $T_N\ge\log_2L_D-O(1)$ (Theorem 3) and $T_N\le C\log_2q_N$ (Theorem 6). The brief's "$T_N\le(1+o(1))\log_2q_N$" is **not** proved for $\ln2$.
* It holds for Lebesgue-a.e. $x$ (Borel–Cantelli: $\sum_D \tau(L_D) L_D^{-c}<\infty$ for every $c>0$, since $\tau(L_D)=L_D^{o(1)}$ covers any accidental gcd drop $q_N\mid L_D$), and it is conjecturally true for $\ln2$. For $\ln2$ without gcd drop it is equivalent to $\eta_{N,L_D}\ge L_D^{-o(1)}$.
* It is also *beaten by generic Dirichlet*: for any real $y=2^N\ln2$ there is an $N$-dependent $q'\le Q$ with $T\approx2\log_2q'$. The $\ln2$-free families sit at $T\approx\log_2q$, half the Dirichlet optimum, because $q\mid L_D$ is fixed by $D$.
* None of this matters for the long-window requirement: even $c=7$ gives $T\le8\log_2q$.

## 6. The window–denominator barrier

The modular-orbit step used in Phase 13 is Vandehey's incomplete-orbit bound. For reduced $a/q$ with $q$ supported on a **fixed finite set $S$ of primes**, $|\sum_{i<L}e(ab^i/q)|\le(A_kq^{\alpha}L^{\gamma}+B_kq^{-\alpha}L^{\nu})(1+\log q)^r$ with $\alpha=1/(2^{k+2}-2)$ and $\gamma=1-\alpha/(k+2)$ ([notes/phase13/quantitative-normality.md](../phase13/quantitative-normality.md)). The first term beats the trivial bound $L$ only for windows $T\ge q^{\delta}$ with $\delta>1/(k+2)$ (in particular $\delta=1/3$ for $k=1$, the square, and $\delta=1/4$ for $k=2$, the cube; the exponents $1/12$ and $1/28$ are the resulting Stoneham discrepancy exponents, not the window threshold). So the hypotheses are:

* **(H1)** the prime support of $q_N$ is contained in a fixed finite set $S$;
* **(H2)** $T_N\ge q_N^\delta$ for a fixed $\delta>0$.

**Theorem 6 (barrier).** Let $\mu'>\mu(\ln2)$ and $Y_N=a/q_N$ reduced with $|2^N\ln2-Y_N|\le2^{-T_N}$. Then

```math
T_N\le(\mu'-1)N+\mu'\log_2q_N+O_{\mu'}(1).
```

Consequently: (i) (H2) forces $q_N\le(c_\delta N)^{1/\delta}$, so $\log q_N=O_\delta(\log N)$; (ii) if $\log q_N\ge\rho N$ then $T_N\le\bigl[(\mu'-1)\tfrac{\ln2}\rho+\mu'\bigr]\log_2q_N+O(1)$, so (H2) fails for all large $N$ and every $\delta>0$.

*Proof.* Put $r=2^Nq_N$. Then $|\ln2-a/r|\le2^{-N-T_N}$; reduce $a/r$ to a fraction with denominator $\le r$ and apply $|\ln2-p/r'|\ge cr'^{-\mu'}$. This gives $N+T_N\le\mu'(N+\log_2q_N)+O(1)$. (i) $q_N^\delta\le T_N\le2.58N+3.58\log_2q_N+O(1)$. (ii) $N\le(\ln2/\rho)\log_2q_N$. $\square$

*Numbers.* With $\mu(\ln2)\le3.57455391$ (Marcovecchio 2009, Thm 1.1; Rukhadze's $3.89139977$ in brackets): the single-pole rate $0.39322$ gives $T_N\le8.11\,[8.99]\log_2q_N$; two-stride $0.26316$ gives $10.36\,[11.51]$; $M=8$ ($0.19661$) gives $12.65\,[14.09]$. The finite exponent $\delta_N=\ln T_N/\ln q_N$ of the correlated Legendre rows is

| $D$ | 24 | 60 | 120 | 240 |
| --- | ---: | ---: | ---: | ---: |
| single pole $\delta_N$ | 0.185 | 0.0792 | 0.0442 | 0.0257 |

It is already below $1/3$ and $1/4$ at $D=24$ and decays like $\ln\log_2q/\log q$. Even a perfect $T=8\log_2q$ would give $\delta_N\to0$. The families also violate (H1): the support is $\{p\le D\}$ (30 of 30 primes at $D=120$, $50$ of $52$ at $D=240$), unbounded.

**What this does and does not rule out.** It rules out every approximant family with $\log q_N\ge\rho N$, in any dimension, at any height, adaptive or not (§7), from supplying (H2). The Phase 16 rate-0 adaptive formulas have $\log q_N=O(N^{2/3})$ (measured $0.07N$ to $0.09N$ at $N=480$); (H2) would need $\log q_N=O(\log N)$, i.e. essentially integer-valued $Y_N$ close to $2^N\ln2$. That is a digit coincidence of $\ln2$ (a long near-periodic block), not an approximation problem. Theorem 6 does not exclude it; it says the approximant route cannot manufacture it.

## 7. E3: feasibility, height, error, window in dimension $k$

Here $\theta_N\in\mathbb Z^k$ ranges over the Phase 16 families (line, plane $u=a=0$, $u=0$, all of $\mathbb Q^4$), cancelled bands are imposed by CRT, and $y_j=d_j\cdot Y(N)$ are the shifted-tail directions ($Ny\approx(0.65,\,1.63,\,0.64,\,0.25)$ at $N=120$).

**Four distinct notions.**
1. *Feasibility*: the CRT coset $\{z:\Pi_v(z)\equiv0\ (M_v)\ \forall v\in B\}$ is non-empty and has index $M=\prod_vM_v\approx e^{mN}$ (Phase 16).
2. *Low height*: some coset point has small $|z|_\infty$.
3. *Small error*: a coset point has $|e_0-z\cdot y|\le\delta$.
4. *Usable window*: $T=\log_2(1/\text{error})-8$ together with (H1)–(H2).

All four are logically independent. In the exact instances below (3) and (4) are separated by Theorem 7(b) and Theorem 6.

**Theorem 7 (E3).** (a) *Band accounting.* For a band $v$ with cancelled prime set $P_v$, $p\in P_v$ divides $q_N$ iff $p\nmid\Pi_v(\theta)=\operatorname{den}(r_v)D\ell_v(\theta)$ (Phase 16 §3). So cancelling band $v$ means $M_v=\prod_{P_v}p\mid\Pi_v(\theta)$: **either** $\Pi_v=0$ (exact vanishing), which costs no height, **or** $|\Pi_v|\ge M_v$, forcing $\ln H\ge (m_v-o(1))N-O(v)-\ln k$ (the $o(1)$ coming from the prime number theorem for $\log M_v$) regardless of $k$. Together, the set $Z$ of exactly vanishing cancelled bands removes $\operatorname{rank}\{\ell_v|_F : v\in Z\}$ linear dimensions (which equals $\#Z$ in the independent-band instances below), leaving effective dimension $k_{\rm eff}=k-\operatorname{rank}\{\ell_v|_F : v\in Z\}$ and $M_{\rm eff}=\prod$ over the non-vanishing cancelled bands.

(b) *Coset ceiling.* Let $D_Y$ be the common denominator of the base value and the $y_j$, and $q^*=D_Y/\prod_{p\text{ cancelled}}p$ (each such $p$ divides $D_Y$ once because $p^2>2N$). Every $\theta$ in the coset has $Y_N(\theta)\in\frac1{q^*}\mathbb Z$, so for **all** such $\theta$, whatever their height,

```math
T(\theta)\le T^*:=\log_2q^*+\log_2\frac1{\eta^*},\qquad\eta^*=\|q^*2^N\ln2\| .
```

Height buys nothing beyond the single coset ceiling $T^*$.

(c) *Minkowski trade-off.* (i) *Homogeneous existence (rigorous).* Let $k\ge2$, $\Lambda\subset\mathbb Z^k$ have index $M$, $Y=|y|_\infty>0$, and $H>\delta/Y$. Then $K=\{|z|_\infty\le H,\ |z\cdot y|\le\delta\}$ contains a sheared parallelepiped (base $[-H_1,H_1]^{k-1}$ in the other coordinates and fiber width $2\delta/Y$ in a coordinate attaining $Y$) of volume $(2H_1)^{k-1}\cdot 2\delta/Y$ with $H_1=(H-\delta/Y)/(k-1)$. By Minkowski there is a non-zero $z\in\Lambda\cap K$ as soon as $H_1^{k-1}\ge MY/\delta$ (here $\ln Y=-\ln N+O(1)$). (ii) *First moment (rigorous for random cosets).* For a uniformly random coset $\{w\cdot z\equiv c\}$ modulo each prime of $P$, the expected number of points of $K$ equals $|\mathbb Z^k\cap K|/M\le(2H+1)^{k-1}(2\delta/Y+1)/M$. (iii) *Threshold law and asymptotic ceiling (heuristic, finite-instance confirmed).* For generic $y$, typical $\eta^*=2^{-o(N)}$, and unsaturated $T$,

```math
(k_{\rm eff}-1)\ln H=\ln M_{\rm eff}+T\ln2+O(1),\qquad T\le T^*-O(1),
```

with asymptotic ceiling $T^*/N\to\rho^*/\ln2$ where $\rho^*=\limsup\frac{\log q^*}N$ (so **window and denominator rate trade one for one**, conditional on $\eta^*=2^{-o(N)}$), and the height needed to reach the ceiling is $H^*=(M_{\rm eff}q^*)^{1/(k_{\rm eff}-1)}$. In rate–height–window form (with $\log M=mN$, $\log H=hN$, $T=\tau N$, rate $\rho\le M_F-m$ by (a) and Phase 16 Theorem 1):

```math
h=\frac{m+\tau\ln2}{k_{\rm eff}-1},\qquad\tau\le\frac{\rho^*}{\ln2}.
```

For $\rho<5/12$ the Phase 16 generic masses $M_F=2/3,\,1,\,2$ give $h>\frac{M_F-5/12+\tau\ln2}{k-1}=\frac14+\tau\ln2,\ \frac7{24}+\frac{\tau\ln2}2,\ \frac{19}{36}+\frac{\tau\ln2}3$ for $k=2,3,4$. At $\tau=0$ this is exactly the Phase 16 conjecture. The additional window cost is $\tau\ln2/(k-1)$, and the asymptotic window rate itself is capped by $\rho^*/\ln2<(5/12)/\ln2=0.60112\ldots<0.6012$.

*Caveat.* (i) and (ii) are rigorous, but the lower-bound half of (iii) is not: $y(N)$ is $g(N\bmod60)/N+O(1/N^2)$ with explicit **rational** $g$ (Phase 16 §6), so genericity of $y$ cannot be proved at polynomial height. Phase 16's gap (an $S$-unit-type problem with moving prime sets) is unchanged.

**Exact instances** (script §3, $N=120$; cancelled bands $k=1:\{5,6,7\}$, $k=2:\{3,5,6,7\}$, $k=3,4:\{2,3,5,6,7\}$, with $u$, hence band 1, left active for $k=4$). "zero" lists cancelled bands that vanish exactly in the minimal solution.

| $k$ | $\log_2M$ | min $\log_2H$ (zero) | $\log_2H,\ \log_2\text{err},\ T$ (target 16) | same (target 32) | $\log q_{\rm odd}/N$ | $T^*$ |
| ---: | ---: | --- | --- | --- | ---: | ---: |
| 1 | 26.5 | 24.4 (–) | error not adjustable | | 0.2975 | 59.3 |
| 2 | 57.1 | 24.4 (3) | 66.6, −20.7, 12 | 80.5, −36.0, 28 | 0.2813 | 59.3 |
| 3 | 110.3 | 24.4 (2,3) | 59.7, −19.9, 11 | 68.1, −36.2, 28 | 0.2813 | 59.3 |
| 4 | 110.3 | 12.1 (2,3,5) | 34.2, −23.3, 15 | 41.0, −38.6, 30 | 1.3026 | 232.5 |

The $k\ge2$ "min height" values coincide with the $k=1$ line or a smaller zero-reduced family because the cancelled bands **vanish exactly** there (item (a)): the per-prime index $M$ overstates the cost. The trade-off scan below uses the effective data (the `log q_odd/N` column is the odd-denominator rate `ev["logq"]` from Phase 16; for $k=4$, the slope is `0.326` across all 6 unsaturated points and `0.332` on the five $k_{\rm eff}=3$ points).

Scan of requested windows (script §3): $c_{\rm eff}=(k_{\rm eff}-1)\ln H-\ln M_{\rm eff}+\ln|\text{err}|$.

| $k$ ($k_{\rm eff}$) | fitted slope $d\ln H/d(\text{bits})$ | theory $\ln2/(k_{\rm eff}-1)$ | spread of $c_{\rm eff}$ (nats) | points |
| --- | ---: | ---: | ---: | --- |
| 2 (2) | 0.669 | 0.693 | 3.06 | $T_{\rm raw}=8.5,17.1,26.4,35.5,39.9$ |
| 3 (3) | 0.355 | 0.347 | 6.46 | $8.7,16.4,28.7,31.8,40.1$ |
| 4 (3) | 0.326 | 0.347 | 3.05 | $11.9,\dots,59.6$ |

At the request $T=56$ the plane reaches only $T_{\rm raw}=47.6$ ($k=2$) and $49.6$ ($k=3$), against the ceiling $59.3$. There $c_{\rm eff}$ jumps from about $-8$ to $+9.9$ and $+10.3$: the **saturation** of Theorem 7(b), not a lattice-reduction failure. For $k=4$ the ceiling is $232.5$ (all of $a,u,b,c$ move the denominators) and no saturation occurs. The luck column $-\log_2\text{err}-\log_2q$ stays $\le5.3$ bits throughout.

**Reading.** In dimension $k$ the cancelled mass $m$ costs $h=m/(k_{\rm eff}-1)$ in height and each bit of window costs $\ln2/(k_{\rm eff}-1)$ more, but the window is capped at the *same* $\log_2q^*$ that the nearest grid reaches. Dimension buys rate and low height; it cannot buy a window beyond $\log_2q^*+O(1)$, and Theorem 6 then forbids (H2).

## 8. E4: $\ln2$, $\pi$, $e$, $\sqrt2$, $\varphi$

All values are exact computations from 32768-bit expansions generated in integer arithmetic (hex prefixes checked), with Fractions for prefixes and continued fractions.

### 8.1 Unified comparison

| | $\ln2$ | $\pi$ | $e$ | $\sqrt2$ | $\varphi$ |
| --- | --- | --- | --- | --- | --- |
| $\mu$ (upper bound) | $\le3.57455391$ (Marcovecchio 2009) / $3.89139977$ (Rukhadze 1987) | $\le7.1032$ (Zeilberger–Zudilin 2020, confirmed) | $=2$ (Euler CF; Davis constant $1/2$) | $=2$ (Pell) | $=2$ (Fibonacci) |
| run after position $N$ of equal digits | $\le2.575N+O(1)$ | $\le6.1032N+O(1)$ | $\le N+\log_2N-\log_2\log N+O(1)$ | $\le N+1.94$ | $\le N+1.694$ |
| rigorous digit statistics | none beyond $\log N$ | none beyond $\log N$ | none beyond $\log N$ | $\gg\sqrt N$ ones (degree 2, BBCP) | $\gg\sqrt N$ ones; $\ge(1-\varepsilon)\sqrt{N/2}$ changes for $1/\sqrt5$ (Kaneko) |
| observed at $N=32704$: ones, $\tau_N$, longest run | 0.5013, 0.5012, 15 | 0.5006, 0.4986, 16 | 0.5009, 0.4983, 18 | 0.4989, 0.5030, 18 | 0.5010, 0.5000, 13 |
| CF, first 300 terms: Lévy $\ln q_n/n$, max $a_n$ | 1.072, 485 | 1.154, 292 | 1.681, 200 | 0.878 (theory 0.881), 2 | 0.479 (theory 0.481), 1 |
| explicit prefix/approximant rate | fixed formula $5/12$; rounded $0.393/0.263/\to0$ (Phase 16); naive $R_N$: $0.97$–$0.99$ | Gaussian model $2/3$ (repo); BBP prefix: $1.46$–$1.52$ | Taylor $A_n/n!$: $0.551\to0.617$ ($n=100\to1600$), $\to\ln2$; convergents: $0.346$–$0.353$ | convergents $\ln2/2$ | convergents $\ln2/2$ |

Observed: every constant has $\tau_N\approx\tfrac12$ and longest run $\le\log_2N+3$; the rigorous growth forms at $N=32704$ are $\sqrt N=181$ (ones, degree 2) and $22$ for $(\ln N)^{3/2}/(\ln\ln N)^{1/2}$ (changes, Bugeaud–Evertse), against $\approx16350$ changes.

**Generic baseline (important).** The Dirichlet value $\ln2/2=0.3466$ is attained by the continued-fraction convergents of *every* irrational, with window $T\approx0$. For $e$ the measured rates at $q\sim2^{102},2^{316},2^{727},2^{1020}$ are $0.3525,0.3482,0.3473,0.3463$. The Phase 16 single-pole rate $0.393$ is therefore *worse* than the generic convergent rate, and only the two-stride ($0.263$) and telescoping ($\to0$) families beat it. A denominator rate $<5/12$ is not a distinguishing arithmetic property by itself; the meaningful pair is $(\text{rate},T)$, and Theorem 7(b) shows $T^*=\rho^*N/\ln2$.

### 8.2 Where the constants differ from $\ln2$

* **$\varphi,\sqrt2$ (quadratic).** Bounded partial quotients give *two-sided* control $\|qx\|\asymp1/q$. Exactly, $|\varphi-p/q|\ge1/((\sqrt5+1)q^2)$ and $|\sqrt2-p/q|\ge1/((2\sqrt2+1)q^2)$, so after position $n$ the run of equal digits is $\le n+1.69$ resp. $n+1.94$; checked for $n<4000$ (max of run$-n$ is $1$ for both). [GoldenOrbit.lean](../../NormalityChecker/GoldenOrbit.lean) turns the digit problem exactly into a Zeckendorf problem: $\varphi^{-(k+1)}\le\|M\varphi\|\le\varphi^{1-k}$ for the least Zeckendorf index $k$ of $M$, and $D^+(\varphi)<1\iff\exists K,\eta>0$ with $\{n<N:k(2^n)\le K\}$ of lower density $\ge\eta$. Verified exactly for all $1\le n<600$. Observed $P(k(2^n)\le K)$ for $K=2,4,6,8,10,12,16,20$: $0.361,0.720,0.871,0.957,0.987,0.993,1,1$, against random integers of equal size $0.396,0.776,0.930,0.968,0.995,0.995,1,1$. At finite scale $2^n$ behaves like a random integer. Positive lower density as $n\to\infty$ is exactly the open statement. This is the one place where the open question is *equivalent* to an arithmetic statement about powers of two, not merely implied by one.
* **$e$.** $\mu(e)=2$ with an explicit Euler CF, so *every* run bound is the sharpest possible. Davis (1978, 1979) proved **both** directions with sharp constant $1/2$: $|e-p/q|<\bigl(\tfrac12+\varepsilon\bigr)\frac{\log\log q}{q^2\log q}$ infinitely often and $|e-p/q|>\bigl(\tfrac12-\varepsilon\bigr)\frac{\log\log q}{q^2\log q}$ for all sufficiently large $q$ (yielding the run ceiling $\le N+\log_2N-\log_2\log N+O(1)$ after position $N$, since $\log\log q/\log q\to0$ weakens the $q^{-2}$ lower bound). Directly on the convergents via $|e-p_n/q_n|=q_n^{-2}(\alpha_{n+1}+q_{n-1}/q_n)^{-1}$, the exact normalized constant $c_n=q_n^2|e-p_n/q_n|\log q_n/\log\log q_n$ achieves its global minimum $0.386249$ over $3\le q\le 10^{602}$ at $n=19$ ($q=10{,}391{,}023$, $a_{20}=14$), and for $q>2^{40}$ its minimum is $0.387300$ at $n=31$ ($a_{32}=22$), approaching $1/2$ slowly from below as $q\to\infty$. In [FactorialNumerators.lean](../../NormalityChecker/FactorialNumerators.lean) the Taylor denominator retains $\log Q_n/\log n!=0.9888,0.9960,0.9970,0.9983,0.9990$ at $n=100,200,400,800,1600$. After the shift the rate is $0.551,0.577,0.594,0.607,0.617\to\ln2$.
* **$\pi$.** The BBP structure is *position-local* (hex digit extraction), not low-denominator: the exact BBP prefix rate is $1.5167,1.4737,1.4634,1.5000$ at hex positions $50,100,200,300$, worse than $\ln2$'s naive prefix ($0.992,0.972,0.978,0.993$ at $N=200..1600$). The only benefit is that the unique-pole prime survival of [BBPDenominator.lean](../../NormalityChecker/BBPDenominator.lean) gives *lower bounds* for denominators, not control of digits. $\mu(\pi)\le7.1032$ against $3.575$ for $\ln2$ leaves a weaker run ceiling ($6.1N$ against $2.6N$).

### 8.3 Why $\sqrt N$ leaves $D^+<1$ open, and citation check

By [transition-discrepancy.md](../transition-discrepancy.md), $D_N\le\max(2/3,1-\tau_N)+1/N$ and $D_\infty<1\iff\liminf\tau_N>0$. The best known lower bounds for quadratics are $\#\{\text{ones}\}\gg\sqrt N$ and, for $1/\sqrt5$, changes $\ge(1-\varepsilon)\sqrt{N/2}$. They give $\tau_N\gg N^{-1/2}\to0$ and $D_N\le1-cN^{-1/2}$, a finite-prefix gap tending to $0$. All these arguments (Ridout and the Subspace theorem; Pell/Zeckendorf identities) penalise a repetition only when it is *long*, of length $\gtrsim\varepsilon\cdot$position. Sparse transitions (average run length $1/\tau\to\infty$) with runs of length $N^{1-\varepsilon}$ never trigger a Diophantine contradiction. Closing the gap from exponent $1/2$ to $1$ requires showing runs are bounded on a positive-density set, which for $\varphi$ is the Zeckendorf statement above.

Literature, as checked by search (the arXiv/publisher pages were read for the cited titles and statements):

| Claim | Status |
| --- | --- |
| BBCP, J. Théor. Nombres Bordeaux 16 (2004) 487–518: $\#1\text{-bits}\ge CN^{1/D}$ for algebraic irrational of degree $D$ | **Confirmed.** The brief attributes this to Bailey–Crandall (2002); that is incorrect. |
| Adamczewski–Bugeaud, Ann. Math. 165 (2007) 547–565: $\liminf p(n)/n=\infty$ for algebraic irrationals | **Confirmed.** Binary expansions of algebraic irrationals are not automatic. |
| Bugeaud, Rend. Sem. Mat. Univ. Padova 118 (2007) 217–233 (digit changes) and Atti Accad. Naz. Lincei 19 (2008) 229–235 (block complexity) | **Confirmed.** Replaces the misstated Palermo 2008 venue in the brief. |
| Bugeaud–Evertse, Acta Arith. 133 (2008) 221–250, arXiv 0709.1560, Thm 3.1: changes $\ge c(\log n)^{3/2}/(\log\log n)^{1/2}$ | **Confirmed.** This is polylogarithmic, not $\sqrt N$. |
| Davis, J. Austral. Math. Soc. 25 (1978) 497–502, and Bull. Austral. Math. Soc. 20 (1979) 407–410: $|e-p/q|<(\frac12+\varepsilon)\frac{\log\log q}{q^2\log q}$ i.o. and $>(\frac12-\varepsilon)\frac{\log\log q}{q^2\log q}$ eventually | **Confirmed** in both directions (sharp constant $1/2$); verified on convergents to $q\sim10^{602}$ here. |
| Zeilberger–Zudilin, Moscow J. Comb. Number Theory 9 (2020) 407–419: $\mu(\pi)\le7.103205334137$ | **Confirmed.** A later preprint claims $7.1018\ldots$; not verified and not used. |
| Marcovecchio, Acta Arith. 139 (2009) 147–184, Thm 1.1: $\mu(\ln2)\le3.57455391$ | **Confirmed** (also cited in `notes/phase13/logarithm-transitions.md`); Rukhadze's $3.89139977$ is also confirmed. No theorem in this note depends on the digits. |

## 9. What is not claimed, and next steps

* No Lean statement was added. Natural next kernel statements: Theorem 1 (Bezout) and Theorem 5 (grid ceiling), both elementary. The Legendre remainder in Theorem 2(b) needs the Laplace integral for $Q_n$, which is not in the library.
* **Do not pursue windows through $\ln2$-free rounding.** By Proposition 4 and Theorem 6 the rounded numerators encode $\ln2$'s own digits and cannot meet (H1)–(H2) at any positive rate.
* The only live arithmetic handles recorded here are (i) the Zeckendorf statement about $k(2^n)$ for $\varphi$ (exactly equivalent to $D^+(\varphi)<1$) and (ii) approximants whose numerators are *not* roundings (the exact Phase 14–15 formulas), where Frobenius structure survives. The first would need an equidistribution statement for the least Zeckendorf index of $2^n$; no tool in the repository proves one.
* Theorem 7(c)(iii) is a heuristic with finite verification at $N=120$ only (the script runs in seconds, so larger $N$ is cheap, but it would not change the status).

## 10. Reproduction

```sh
python -B scripts/phase17_classical_approximants.py   # about 4 seconds
```

The program is dependency-free apart from importing, read-only, [phase16_adaptive_log.py](../../scripts/phase16_adaptive_log.py) for the exact cell rows, LLL and congruence helpers of E3. It ends with `All Phase 17 Track E classical-approximant checks passed`. Sections: 0 self-tests (kernel coefficients against recurrences, pole identities exact, remainder identity against quadrature); 1a analytic remainders; 1b certified table (40 rows asserted); 1c prime support; 1d the luck experiment; 1e barrier constants; 3 E3; 4 E4.
