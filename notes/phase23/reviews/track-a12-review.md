# Referee report: Phase 23 Track A1–A2

**Audited files (read-only):** `notes/phase23/euler-square-and-higher-order-tower.md` (the "note", 277 lines) and `scripts/phase23_euler_tower.py` (the "script", 391 lines).
**Author model:** `gpt-6.2-astra`. **Referee model:** `claude-opus-5-5` (cross-provider).
**Date:** 2026-11-27.

> **Scope disclaimer.** This is a cross-model review. It is **not** independent human peer review. The script's finite computations and my own recomputations are finite certificates or measurements. They prove no asymptotic theorem. Every asymptotic claim below was checked by reading the argument.

## Verdicts

| Sub-track | Verdict | Critical | Major | Minor |
|---|---|---:|---:|---:|
| **A1** ($E_2^2$: preceding-gap identity, carry flips, the $1/40000$ bound) | **ACCEPT AFTER REVISION** (minor, presentation only) | 0 | 0 | 7 |
| **A2** (tower $b^L\mid k$, discrepancy spectrum, finite spectra, Lean blueprint) | **ACCEPT AFTER REVISION** (minor, presentation only) | 0 | 0 | 6 |

I found no mathematical error in either sub-track. Every constant, sieve parameter, Wirsing constant and arithmetic inequality behind $1/40000$ checks out. Binary simple normality of $E_2^2$ stays **Open** throughout, with no overclaim.

---

## 0. Reproduction of the script

* `python -B scripts/phase23_euler_tower.py` ran on Windows (CPython). **It exited with code 0** in about 2.6 s and printed `All exact finite checks passed.`
* Printed output compared with the note:

| Note location | Note value | Script output | Match |
|---|---|---|---|
| l. 261, $N=4096$ | 1762, 884, 2119, 2106, 2076, 90 | `4096 1762 884 2119 2106 2076 90` | ✔ |
| l. 262, $N=16384$ | 6376, 3190, 8304, 8275, 8216, 323 | `16384 6376 3190 8304 8275 8216 323` | ✔ |
| l. 263, $N=32768$ | 12187, 6095, 16545, 16510, 16422, 686 | `32768 12187 6095 16545 16510 16422 686` | ✔ |
| l. 269, $(2,1,2)$ | 1, 2/3, 2/3 | `1 2/3 2/3` | ✔ |
| l. 270, $(2,1,4)$ | 2, 2/5, 2/3 | `2 2/5 2/3` | ✔ |
| l. 271, $(2,2,4)$ | 1, 2/5, 2/5 | `1 2/5 2/5` | ✔ |
| l. 272, $(2,3,8)$ | 1, 229/1020, 229/1020 | `1 229/1020 229/1020` | ✔ |
| l. 273, $(3,2,9)$ | 12, 17789/88569, 6226/29523 | `12 17789/88569 6226/29523` | ✔ |
| l. 137 | $1/40000$, $39999/40000$, $19999/40000$; $K_*<5000$ | asserted in `check_frequency_constants` (script ll. 167–174) | ✔ |

* **Independent recomputation.** I wrote a separate brute force (scratch file, not committed). It enumerates every block of length $k$ and keeps the $L$-balanced ones. Then it computes the extreme interval discrepancy as the oscillation of $F(x)-x$ over all pre- and post-jump values, with the endpoints included. This does not use the script's integer formula (9) or its Euler-tour enumerator. All five spectrum rows of the table were reproduced exactly. Every value obeyed $D\le 2/b^L$.
* I imported the script's functions and found that no gap containing $N$ is flipped for any of the three $N$. The gaps are $[4095,4098)$, $[16383,16388)$ and $[32765,32770)$. So the clipping wording issue A1-m5 does not change any number.

---

## 1. Sub-track A1: $E_2^2$

### 1.1 Preceding-gap signed identity (note ll. 37–43, 69–77): verified

* **Tail identity (l. 43).** Take $m_{i-1}\le n<m_i$. The first supported index after $n$ is $m_i$, so $T_n=2^{n-m_i}(a(m_i)+T_{m_i})=2^{n-m_i}V_{m_i}$. Correct. The sign comes from the **right endpoint** $m_i$, so the gap carrying that sign is $g(m_i)=m_i-m_{i-1}$, the gap **preceding** $m_i$. This is the correct orientation, and the note states it explicitly at l. 77. The forward-gap form $s(m_{i+1})(m_{i+1}-m_i)$ is flagged as needing an extra correlation identity, which is also correct. The next $L$ digits are $0^L$ if $0<T_n<2^{-L}$ and $1^L$ if $-2^{-L}<T_n<0$, because then $\{T_n\}=1+T_n$. Correct.
* **$V_m\ne0$.** $T_{m-1}=V_m/2$, and $T_{m-1}\equiv 2^{m-1}E_2^2 \pmod 1$, so $V_m\ne0$ follows from irrationality. Phase 20 §4 proves this by Nesterenko (`notes/phase20/euler-product.md`, l. 186). The note does not link it (A1-m4).
* **Error budget for (4).** Each exceptional shift changes the difference of counts by at most 2. The partial gap at $N$ is $O(\sqrt N)$, because $12(3j^2+j)+1=(6j+1)^2$ lies in $U$: a square has even exponents at every prime outside $1 \bmod 12$, and $c(p^{2e})\ne0$. Consecutive such indices differ by $6j+4$. The exceptional count is $O(N\log\log N/A_N)=O(\log A_N/A_N)\cdot N$, which is dominated by $(\log A_N/A_N)^\theta$ because $\theta<1$. Correct.

### 1.2 Negligible total gap weight of carry flips (ll. 53–67): verified

* A flip $\operatorname{sgn}V_m\ne s(m)$ forces $|T_m|>|a(m)|\ge1$. Correct.
* Ends with a support point in $(m,m+R]$ number at most $\sum_{h\le R}P_h(N)\le C_0RN/A_N^2$, by Phase 22 Theorem S, which is uniform for $1\le H\le N$ (`notes/phase22/partitions-carry-and-lemma-s.md`, l. 39). For an isolated end, Markov's inequality gives $\#\le\sum_{j>R}2^{-j}\sum_{m\le N}|a(m+j)|\ll\sum_{j>R}2^{-j}(N+j)\ll(N+R)2^{-R}$. Correct.
* With $R=\lceil3\log_2A_N\rceil$ we get $|\mathcal B_N|\ll N\log A_N/A_N^2$. Hölder with exponents $\gamma/(\gamma-1)$ and $\gamma$, together with (2), gives
  $(N\log A/A^2)^{1-1/\gamma}(NA^{\gamma-1})^{1/\gamma}=N(\log A)^\theta A^{-2\theta+\theta}=N(\log A/A)^\theta$,
  where $\theta=1-1/\gamma\in(0,1/3)$ for $\gamma\in(1,3/2)$. Correct.
* **External input (2): Matomäki–Radziwiłł, Corollary 1.2(ii).** I checked the published statement in arXiv:2007.04290 v1, HTML version, §1.1. Hypothesis (2) there requires, for some $\alpha>0$ and all $w\le z\le X^\alpha$, that $\sum_{w<p\le z,\,p\in\mathcal N}1/p>\alpha\sum_{w<p\le z}1/p-O(1/\log w)$. The conclusion, for $\gamma\in[1,3/2)$, is $\sum_{n_i\le X}(n_{i+1}-n_i)^\gamma\asymp_{\alpha,\gamma}X\delta(\mathcal N;X)^{1-\gamma}$, where $\delta(\mathcal N;X)=\prod_{p\le X,\,p\notin\mathcal N}(1-1/p)$.
  * $\mathcal N=\{m:c(m)\ne0\}$ is a multiplicative set in their sense, because $c$ is multiplicative.
  * Every element is $\equiv1 \bmod 12$, so $\mathcal N=12U+1$ exactly.
  * The primes of $\mathcal N$ have relative density $1/4$, so the hypothesis holds with $\alpha=1/8$, uniformly in $z$.
  * $\delta\asymp(\log X)^{-3/4}$, because the excluded primes are $2$, $3$ and $\mathcal P$, with density $3/4$.
  * Each preceding gap $g(m)$ with $m\le N$ is $1/12$ of an MR forward gap whose left endpoint is $12m_{i-1}+1\le 12N+1=X$.

  The application is valid. Corollary 1.2(ii) asserts no relation between $\alpha$ and the range of $\gamma$, so taking $\gamma<3/2$ is exactly their range.

### 1.3 The shifted-correlation test (5) and the layer bound (ll. 79–93): verified

* At $m\in U$, the conditions $j<\min(H,m)$ and "no support in $[m-j,m-1]$" leave exactly $\min(g(m),H)$ values of $j$. This includes $m=m_1$, where the product never reaches index $0$. The truncation loss is $\sum_{g>H}g\le H^{1-\gamma}\sum g^\gamma\ll N(A/H)^{\gamma-1}$. Correct. Hence (5) holds for every $H_N/A_N\to\infty$.
* **Layer bound (l. 93).** In layer $j$, a discarded end $m$ has its immediate predecessor $m'\in[m-j,m-1]$. Either $m'=0$, which happens for one end only ($m=m_1$), or $(m',m)$ is a pair with $1\le h\le j$ and $1\le m'\le N$. Summing $1+C_0jN/A^2$ over $j<H$ gives $H+C_0H(H-1)N/(2A^2)$. Correct. The script checks a sharper, weighted form of this inequality exactly (script ll. 143–149).

### 1.4 The unconditional bound $1/40000$ (ll. 95–137): every constant re-derived

1. **Layer optimization.** At $H=\lfloor tA\rfloor$ the bound is $W_\sigma/N\ge tC_\eta/2-C_0t^2/2+o(1)$. Its maximum is at $t=C_\eta/(2C_0)$, with value $\kappa=C_\eta^2/(8C_0)$. Since $W_++W_-=N+O(\sqrt N)$ and (4) holds, $f_0=W_+/N+o(1)$. Correct. This uses $S_\pm(N)\sim C_\eta N/(2A_N)$, the signed-Wirsing deduction of Phase 22 (A1-m6).
2. **Wirsing constant $W$ (ll. 114, 119).** Wirsing's theorem gives $S(N)\sim\frac{e^{-\gamma_E/4}}{\Gamma(1/4)}\frac{X}{\log X}\prod_{p\le X}(\text{local factor})$, with $\tau=1/4$. Expanding the product:
   * $\prod_{p\equiv1(12)}(1-1/p)^{-1}=e^{\gamma_E}\log X\cdot\tfrac13\cdot P(X)\,(1+o(1))$;
   * the factor at $\mathcal P$ is $\prod(1-p^{-2})^{-1}$;
   * $X=12N$.

   Together these give $S(N)\sim W\,N\,P(X)$, where $W=4e^{3\gamma_E/4}\Gamma(1/4)^{-1}\prod_{\mathcal P}(1-p^{-2})^{-1}$. Hence $P(z)\sim(C_\eta/W)(\log z)^{-3/4}$. Correct.
3. **Sieve.** I compared this with Phase 22, Lemmas S.1–S.4 and §1.4.
   * Lemma S.1 gives $X/G(\xi)$. Lemma S.2 gives $G(\xi)\ge\frac12\prod_{\mathcal Q}(1-1/p)^{-\rho(p)}$ when $\xi\ge z^{17}$ and $\log z\ge2$.
   * The progression length is $\le N/d+1=(1+o(1))N/d$ because $d\le V^4=(\log N)^{12}$.
   * Primes $p\mid vv'$ contribute $\le(v/\varphi(v))^2(v'/\varphi(v'))^2$. Primes $p\mid h$ with $\rho(p)=1$ contribute $\le h/\varphi(h)$.
   * The remainders total $V^2\xi^2(1+\log\xi)^2=N^{34\beta}(\log N)^{O(1)}=o(N/A^2)$, exactly because $\beta<1/34$.
   * The class with $v>V$ costs $O(N/V+\sqrt N)=o(N/A^2)$ per $h$, because $V=(\log N)^3$.

   The main-term constant $2+o(1)$ is correct.
4. **Sum over $(v,v')$.** The map $(v,v')\mapsto(g,w,w')$ is injective, $d=g^2w^2w'^2$, and $v/\varphi(v)\le(g/\varphi(g))(w/\varphi(w))$. The prime factors of $v$ lie in $\mathcal P$, so they are coprime to 6. Hence the sum is $\le J_4J_2^2$. Correct.
5. **Divisor sum.** $\sum_{h\le H}h/\varphi(h)\le H\prod_p(1+1/(p(p-1)))=H\zeta(2)\zeta(3)/\zeta(6)<2H$. Correct. Note that $R$ here collides with $R$ at l. 59 (A1-m3).
6. **Assembly.** $P(z)^2\sim(C_\eta/W)^2\beta^{-3/2}A_N^{-2}$, which gives $\limsup A^2\sum_{h\le H}P_h/(HNC_\eta^2)\le2\beta^{-3/2}J_4J_2^2R/W^2$, uniformly in $H$. Letting $\beta\uparrow1/34$ after the limsup gives $K_*=2\cdot34^{3/2}J_4J_2^2R/W^2$. Taking $C_0=(K_*+\varepsilon)C_\eta^2$ for large $N$ gives $\kappa=1/(8K_*)$, and $C_\eta$ cancels. Correct.
7. **Numerical inequalities:**
   * $\Gamma(1/4)\le\int_0^1t^{-3/4}dt+\int_1^\infty e^{-t}dt=4+e^{-1}<5$, and $e^{3\gamma_E/4}\ge1$ with the $\mathcal P$-product $\ge1$, so $W>4/5$. ✔
   * $(1-u)^{-4}$ is convex with value $(5/4)^4=625/256\approx2.441\le1+8/5$ at $u=1/5$, so the chord gives $(1-u)^{-4}\le1+8u$ on $[0,1/5]$. The same bound holds for $a=2$. ✔
   * $\sum_{n\ge5}n^{-3}\le\int_4^\infty x^{-3}dx=1/32$, so the Euler product is $\le e^{1/4}\approx1.284<4/3$. ✔
   * $\sum_{n\le6}n^{-2}+1/6\approx1.658<5/3$. ✔
   * The Euler-product identity for $J_a$ is correct, with $(2/3)\zeta(2)=\prod_{p\ge5}(1-p^{-2})^{-1}$. This gives $J_a<\frac23\cdot\frac53\cdot\frac43=\frac{40}{27}<\frac32$. ✔
   * $K_*<2\cdot36^{3/2}\cdot(3/2)^3\cdot2\cdot(5/4)^2=4556.25<5000$, so $\kappa>1/40000$. ✔
   * *Informational (floating point, not a proof):* the actual values are $J_4\approx1.1904$, $J_2\approx1.1342$, $W\approx1.8512$ and $R\approx1.9436$. These give $K_*\approx344.3$ and $1/(8K_*)\approx1/2755$, so $1/40000$ is valid but loose by a factor of about 14.5.
8. **No overclaim.** Simple normality is labelled **Conditional** on cancellation in (5) and **Open** otherwise (ll. 5, 93, 108). The finite Euler data are explicitly said to establish nothing asymptotic (l. 275). ✔

### 1.5 A1 Minor findings

| ID | Line(s) | Finding | Fix |
|---|---|---|---|
| A1-m1 | 5 | The summary bullet labels the $1/40000$ bound and (4) simply as "Paper proof". Both depend on **External input**: Serre's CM identification, signed Wirsing for $S_\pm$, and Matomäki–Radziwiłł Cor. 1.2(ii). The repository's label policy asks for these to be separated. | Relabel as "Paper proof from external inputs (Serre; Wirsing; Matomäki–Radziwiłł Cor. 1.2(ii))". |
| A1-m2 | 110 | "one can use $\kappa=1/40000$, independently of the choice of $C_0$" reads as if $\kappa$ in (6) did not depend on $C_0$. In fact $\kappa=C_\eta^2/(8C_0)$, and the point is that $C_0$ may be taken as $(K_*+\varepsilon)C_\eta^2$. | Reword: "Taking $C_0=(K_*+\varepsilon)C_\eta^2$ in (6), valid for large $N$, gives $\kappa\ge1/(8K_*)>1/40000$." |
| A1-m3 | 59/128; 95/114; 113/121/202/255 | Notation collisions: $R$ is both the isolation radius and $\prod(1+1/(p(p-1)))$. $W_\sigma$ (weights) sits beside the constant $W$. $P$ means $P(z)$, $P_h(N)$, the final computed index (§7) and the copy count (§5). | Rename, for example $R\to R_0$ at l. 59, $W\to\mathcal W$, and $P\to P_{\rm end}$ in §7. |
| A1-m4 | 43 | "$V_m\ne0$ by irrationality of $E_2^2$" has no citation. | Link Phase 20 §4 (`../phase20/euler-product.md`, Nesterenko transcendence). |
| A1-m5 | 257 vs script ll. 120, 126 | The note says the flipped weight "counts all starts in gaps", which implies no clipping. The script clips the last gap to $[0,N)$, the same as the positive-weight columns. I checked that this is immaterial for the three $N$, since no gap containing $N$ is flipped. | Say "counts starts in $[0,N)$ in gaps whose right endpoint …". |
| A1-m6 | 101–108 | The optimized constant uses the equal sign split $S_\pm\sim C_\eta N/(2A_N)$. The note cites it at l. 33 but does not repeat it where (6) is derived. | Add "using $S_\sigma(N)\sim C_\eta N/(2A_N)$ (§1)" at l. 101. |
| A1-m7 | 51 | The MR anchor `#page=3` is unverified: I could read only the HTML version, which has no pages. The quoted hypothesis is also missing the range "$w\le z\le X^\alpha$" and the strict "$>$". Both are satisfied here. | Quote hypothesis (2) verbatim with its range, and check the page anchor. |

*Optional, not a defect:* at the measured $N$, $f_0-f_1$ and $\frac1N\sum s(m)g(m)$ still differ noticeably: $0.0347$ vs $0.0139$ at $N=4096$, and $0.0098$ vs $0.0024$ at $N=32768$. This fits the slowly decaying error $(\log A_N/A_N)^\theta$. One sentence saying so would stop readers from treating the table as a test of (4).

---

## 2. Sub-track A2: the tower and the spectrum

### 2.1 Decomposition (7) and cylinder stability (ll. 141–150): verified

* $y\in Q^{-1}\mathbb Z\cap M_{b^k}$ gives $\|b^{kn}y\|=\|y\|$, because $b^k\equiv1\bmod Q$. So $y\in\mathbb Z$. Uniqueness then follows from $M_{b^k}=M_b$, which is the kernel-verified `RadixPowerTower.zeroOrbitSubgroup_pow_eq` (RadixPowerTower.lean l. 694, present).
* The test $z\in K_b\iff Q\mid(b-1)r$ holds in both directions: the difference of the two fixed-point parts lies in $Q^{-1}\mathbb Z\cap M_b=\mathbb Z$, using $(b-1)\mid Q$. ✔
* **Coprime-rational cylinder stability.** $0<r'<Q$ and $\gcd(b,Q)=1$ give $r'b^\ell-jQ\ne0$, so the margin to the $b^{-\ell}$ grid is $\ge1/(Qb^\ell)$ on **both** sides. This includes the margin from $0$ and from $1$, so a small signed perturbation never wraps. By Markov, the remaining starts have density $\le Qb^\ell m_N(u)\to0$. ✔ The cited Lean theorem `coprime_rat_cylinder_stable` exists at RadixPowerTower.lean **l. 1012**, with the strict two-sided margin as stated.

### 2.2 Necessity and sufficiency of $b^L\mid k$ (ll. 152–158): verified

* **Necessity.** Outside $K_b$ we have $r\ne0$. The limiting $L$-word frequencies are cyclic counts over a least period $d\mid k$. Frequency $1/M$ forces each count to equal $d/M\in\mathbb Z$, so $M\mid d\mid k$. ✔
* **Sufficiency.** The de Bruijn multigraph is balanced (in-degree = out-degree $b$) and strongly connected, so an Euler circuit exists. For $L=1$ the $b$ labelled loops are kept. The cyclic word $W$ of length $M$ has least period $M$, since a shorter period would repeat an $L$-window. Repeating it $k/M$ times gives $L$-balance. Orbit size $M\ge2$ means $c$ is not a fixed point, which is equivalent to $Q\nmid(b-1)r$. Then $z\notin K_b$, while $z\in K_{b^k}$ by (7). ✔
* **Exact-order witness.** Every $L$-word occurs once in $W$ and has a unique follower. So among the $(L+1)$-words with that prefix, one has frequency $1/M$ and the other $b-1\ge1$ have frequency $0$. Hence $z$ is not $(L+1)$-normal. ✔
* **Irrational perturbation $u=\sum_jb^{-2^j}$.** Positions with a $1$ within the next $J$ digits number $O(J\log(N+J))$. Elsewhere $\{b^nu\}<b^{-J}$, so $u\in M_b$. The expansion is not eventually periodic, so $u$ is irrational, and so is $c+u$. ✔
* **$(b,L)=(2,1)$ versus the rest.**
  * For $b\ge3$, $K_b$ has no simply normal element. In the case $x=w\in M_b$, the digits $0$ and $b-1$ have total frequency one. For an interior fixed point, its own digit has frequency one.
  * $K_2=M_2$ has no 2-normal element, because the mixed words $01$ and $10$ have frequency 0.
  * The run construction $1,2,3,\dots$ lies in $M_2$ (the boundary starts are $O(J\sqrt N)$) and is simply normal.

  So "existence in $K_{b^k}$ $\iff$ $M\mid k$ or $(b,L)=(2,1)$", while the difference of kernels always needs $M\mid k$. ✔ This matches Phase 22 §10.

### 2.3 Exact fixed-level spectrum (ll. 160–184): verified

* **Equal-atom formula.** $D=1/d+\max_i(y_i-i/d)-\min_i(y_i-i/d)$. I re-derived it from the pre- and post-jump values of $F(x)-x$, together with the value $0$ at the endpoints, which always lies between the two extremes. It holds for multisets with ties, using the first and last ranks within each tie. ✔ The extreme interval discrepancy on $[0,1)$ equals the circle-arc discrepancy, since a wrapping arc's excess is the deficit of the complementary interval. This is why the script's arc-based `direct_discrepancy` (script ll. 200–206) is a valid independent check (A2-m4).
* **(8).**
  * $D_\infty=(1+\max y-\min y)/M$, because $t_j=T^Ly_j$ permutes the orbit.
  * From $Mx\le1-z$ and $Mz\le1-x$ we get $(M+1)(x+z)\le2$, hence $D\ge2/(M+1)$.
  * The digit after the unique $0^L$ is nonzero, which gives $bMx=d+y'\ge1+x$. With the complementary bound for $z$, $D\le\frac2M\bigl(1-\frac1{bM-1}\bigr)$.

  ✔ Both bounds are tight at $(2,1,2)$, where $D=2/3$ is both the upper and the lower bound.
* **(9).**
  * $L$-balanced cyclic blocks correspond to Euler tours of the $t$-fold multigraph that start at $0^{L-1}$. Every block visits $0^{L-1}$ because $0^L$ occurs, and the wrap-around windows are consistent because the tour returns to $0^{L-1}$.
  * $D_\infty(z)=D(\mu_c)$ by Phase 22 Thm 9.2, which is present at `odd-characters-and-kernel-quotient.md` l. 434.
  * Every value is attained by an irrational.
  * The exact-order filter (counts $k/(bM)$) is correct, and the script implements it at l. 241.
  * The bound $D_\infty\le2/M-2/(MQ)$ is correct. Each point lies at least $1/(MQ)$ from the $M$-grid, and with ranks $i=jt+s$ the oscillation is at most $2/M-2/(MQ)-1/k$.

  ✔

### 2.4 Spectrum over all reals (ll. 186–204): verified

* **Universal bound.** Outward rounding of the endpoints bounds the excess by $2/M$. Inward rounding bounds the deficit, and an empty inner rounding means $c-a<2/M$. Hence $D^+\le2/M$ for every $L$-normal real. ✔
* **Realization of $\alpha=2t/M$ for every $t\in[0,1]$.**
  * $\nu$ is shift-invariant (rotation permutes the $L$-words) with a uniform $L$-marginal.
  * The block construction $w^j$ (of length $jL$, a multiple of $L$) gives every phase exactly $j$ times, up to $O(\ell)$ boundary starts. The normal pieces form one initial segment of a normal stream. The boundary and unfinished-stage errors are $O(J)$ against a length of order $J^2$.
  * On the $b^\ell$ grid the uniform component cancels exactly, which gives the upper bound $2t/M$. The interval $[1/B,1-1/B)$ has deficit exactly $2t(1/M-1/B)$, because under $\nu$ only $w=0^L$ and $w=(b-1)^L$ reach the outermost cells. The rounding bound $2/B$ holds for every empirical measure. Taking $N\to\infty$ and then $\ell\to\infty$ gives $D_N\to2t/M$, including $t=1$.

  ✔
* **Exact order and exclusion of 0.** $f_{0^{L+1}}\to(1-t)/(bM)+t/M\ne1/(bM)$ for $t>0$. Conversely, $D_N\to0$ forces normality. So the spectrum is $[0,2/M]$ over all $L$-normal reals and $(0,2/M]$ for exact order $L$. ✔
* **Density across tower levels.**
  * Take $P$ copies of an order-$J$ de Bruijn cycle and insert $q$ laps of each rotation-orbit walk at its base vertex. The insertions return to the same vertex, so the $L$-counts are exactly $Pb^{J-L}+q$.
  * The level is $k=Pb^J+qM$, a multiple of $M$, and the inserted fraction tends to $t$.
  * The cell masses differ from the mixture by at most `changed`$/k=O(JM)/k$ on every grid interval. The signed sum over a sub-interval is bounded by the larger of the positive and negative parts, each at most `changed`. So the script's bounds at ll. 382–383 are valid.
  * The $0^{L+1}$ excess $q(1-1/b)-O(JM)>0$ gives exact order $L$ eventually.
  * The closure is $[0,2/M]$, including the exact-order filter. The variant with all large multiples $k$ (a fixed circuit plus $k/M-1$ laps) is also correct.

  ✔

### 2.5 Lean 4 blueprint (ll. 206–251): consistent with the repository

* `SimpleNormalityKernel.wordFreq (b L : ℕ) (x : ℝ) (v N : ℕ) : ℝ` exists (l. 73), and the partial application `wordFreq b L x v : ℕ → ℝ` type-checks in shape.
* `RadixPowerTower.zeroOrbitSubgroup` (l. 656), `zeroOrbitSubgroup_pow_eq` (l. 694) and `coprime_rat_cylinder_stable` (l. 1012) all exist.
* `radixDiscrepancy` lives in `NormalityChecker` (`BinaryDiscrepancy.lean` l. 11) and is reachable transitively through `SharpTranslation`.
* `NormalityChecker/HigherOrderTower.lean` does not exist yet, so there is no name clash. The note correctly says that no new kernel-verified declaration exists (l. 208).
* `cyclicCount` reads the $L$-word at shift $j$ as $\lfloor b^L(b^jr\bmod q)/q\rfloor$, which agrees with `wordAt` on the rational orbit. `exists_balanced_block`, `tower_iff` and `tower_irrational_exact_iff` state exactly the paper theorems.

### 2.6 A2 Minor findings

| ID | Line(s) | Finding | Fix |
|---|---|---|---|
| A2-m1 | 265–273 | The table lists the **full** $L$-normal spectrum, without the exact-order filter. The caption does not say so. The two differ at $(2,1,4)$: the value $2/5$ comes from `0011`, which is 2-normal, so the exact-order-1 spectrum is $\{2/3\}$ alone. My brute force confirms that the other four rows are unchanged by the filter. | Add "(all $L$-normal elements; with the exact-order filter, $(2,1,4)$ has the single value $2/3$)". |
| A2-m2 | 204 | "each group is inserted once": the script concatenates **several** orbit walks that share a base vertex into one insertion (script l. 333). The junctions are therefore counted per orbit, not per group. The bound $O(JM)$, specifically $\le2M(J-1)$ as at script l. 378, still holds. | Say "at most one junction pair per rotation orbit, hence at most $2M(J-1)$ affected starts". |
| A2-m3 | 210–249 | The repository's Lean files begin with `module` and use `public import`. The blueprint uses plain `import`, and its `theorem` targets have no `:= by sorry` placeholders, so pasting the block into a file will not compile. | Add `module` / `public import`, and mark the targets with `sorry`, or label the block as pseudocode. |
| A2-m4 | 3, 162 | $D_N$ is defined over intervals in $[0,1]$, but the formula in §4 and the script's checker use circle arcs ("seam identified"). The two extreme discrepancies are equal, but the note never says why. | Add one sentence: a wrapping arc's excess equals the deficit of the complementary interval, so the two suprema coincide. |
| A2-m5 | 182 | "Discard tours in which every length-$(L+1)$ word occurs $k/(bM)$ times" is correct but compressed. | Say "discard tours that are $(L+1)$-balanced, i.e. every $(L+1)$-word occurs exactly $k/(bM)$ times (possible only when $bM\mid k$)". |
| A2-m6 | 6–7 | The summary bullets cite the Phase 19 decomposition and Phase 22 Thm 9.2 only in the body. | Name these inputs in the bullet, in line with the evidence-label policy. |

---

## 3. Script audit (independent of the note's numbers)

* **Euler section.**
  * The pentagonal convolution, the Gaussian-generator count, the prime-power formula and the dilation identity (1), checked at $p=13,37,61,73,97$, are mutually consistent over the whole computed range (script ll. 30–74).
  * The tail enclosure is rigorous. It starts from $|T_P|\le P+3$, which follows from $|a(m)|\le\#\{\text{generalized pentagonal numbers}\le m\}\le m+1$, rounds outward, and requires the floors of both endpoints to agree.
  * A second, single-enclosure certificate of the prefix agrees with the first (script ll. 111–114).
  * The bound $|a(m)|\le m+1$ is not asserted in the script. It is a proof-level bound, needed beyond the computed range anyway, and it is correct.
* **Tower section.**
  * Brute force over all binary blocks with $k\le9$ ($L\le3$) and all ternary blocks with $k\le6$ ($L\le2$) is compared against traversal and against an arc-based discrepancy (script ll. 247–270).
  * The fixed-level bound $2/M-2/(MQ)$, (8), repetition invariance and the follower property are all asserted.
* **Mixture section.**
  * Exact grid masses for $t\in\{0,2/5,1\}$, together with the outer-cell deficit.
  * Spliced cycles with exact $L$-balance, the junction bound and the exact-order check.
* All arithmetic is exact (integers and `Fraction`). There are no floating-point tolerances.

## 4. Summary for the author

**A1 and A2 are mathematically sound as written.** None of the 13 findings changes a theorem, constant or number. Most concern evidence labelling and notation; the rest are wording and presentation. The $1/40000$ chain checks out step by step, and the true sieve-optimized constant is about $1/2755$ by a floating-point estimate, which is not a proof. Binary simple normality of $E_2^2$ remains **Open**, and the note never claims otherwise.

*Reminder: this cross-model review is not independent human peer review. The finite checks, the script's and the referee's alike, do not prove the asymptotic statements.*
