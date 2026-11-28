# The original classical constants: mesoscopic carry collisions for $E(2)$ and $E_+(2)$, dynamic rigidity and a reset barrier for $\ln 2$, and a band law for $e$

Phase 25, Track G (G1–G4). This note continues [classical-constants-and-joint-numerators.md](../phase24/classical-constants-and-joint-numerators.md) (`GF-40`, cited as *P24-E*), [classical-correlations-and-log2.md](../phase23/classical-correlations-and-log2.md) (`GF-35`, cited as *P23-E*), [dense-digit-mass-and-lambert.md](../phase24/dense-digit-mass-and-lambert.md) (`GF-36`, cited as *P24-A*), [erdos-borwein-bias.md](../phase17/erdos-borwein-bias.md) (`CC-49`, cited as *P17*) and [classical-targets-and-recon.md](../phase22/classical-targets-and-recon.md) (`GF-28`). Companion script: [`scripts/phase25_classical.py`](../../scripts/phase25_classical.py).

## 0. Definitions, notation and labels

**Radix notation.** For $x\in\mathbb R$ and radix $2$, $d_j=d_j(x)$ is the $j$-th binary digit of $\{x\}$ (expansion not ending in $1^\infty$), $f_1(N)=\frac1N\#\{j\le N:d_j=1\}$, $D_N(x;2)$ is the extreme discrepancy of $(\{2^nx\})_{0\le n<N}$, $D^\pm=\limsup/\liminf D_N$, $S_N(1;x)=\frac1N\sum_{n<N}e(2^nx)$ with $e(t)=e^{2\pi it}$, and $\|t\|$ is the distance to $\mathbb Z$. For $c\in\mathbb Z$, $s_2(c)$ is the binary digit sum of $|c|$ and $w_\pm(c)$ the minimal signed-digit weight, attained by the non-adjacent form (NAF; Reitwiesner 1960).

**Erdős–Borwein constants.** $E=E(2)=\sum_{n\ge1}\tau(n)2^{-n}$ and $E_+=E_+(2)=\sum_{n\ge1}a_+(n)2^{-n}$ with $a_+(n)=\sum_{d\mid n}(-1)^{d-1}=(1-e)\tau(m)$ for $n=2^em$, $m$ odd (Lean `erdosBorweinPlusCoeff_eq`). Write

```math
\tau(n)=2^{V(n)}U(n)\quad(U(n)\text{ odd}),\qquad V(n)=\sum_{p^{f}\parallel n}v_2(f+1),\qquad U(n)=\prod_{p^f\parallel n}\operatorname{odd}(f+1).
```

$V$ is additive and $U$ multiplicative; $U(n)\ne1$ only if $p^2\mid n$ for some $p$. $\omega(n)$ is the number of distinct prime factors and $R(n)=V(n)-\omega(n)=\sum_{p^f\parallel n,\,f\ge2}(v_2(f+1)-1)$.

**Column process of $E$.** Let $B(n)=\{i\ge0:\text{bit }i\text{ of }U(n)\text{ is }1\}$. Since $\tau(n)2^{-n}=\sum_{i\in B(n)}2^{-(n-V(n)-i)}$, source $n$ deposits one bit in **column** $j(n,i)=n-V(n)-i$ for each $i\in B(n)$. Here $j(n,i)\ge1$, because $2^{V(n)+i}\le2^{V(n)}U(n)=\tau(n)\le n<2^n$. Put $S_j=\#\{(n,i):j(n,i)=j\}$, so $E=\sum_{j\ge1}S_j2^{-j}$. A **collision pair at distance $h\ge1$** is an unordered pair of bits $(n,i)$, $(n+h,i')$ with $i\in B(n)$, $i'\in B(n+h)$ and $j(n,i)=j(n+h,i')$, equivalently

```math
V(n+h)-V(n)=h+i-i'. \tag{0.1}
```

Two bits of one source never share a column, so $\sum_{j\le N}\binom{S_j}2$ counts the collision pairs in columns $\le N$.

**BBP states of $\ln 2$.** $s_n=\sum_{k\le n}2^{n-k}/k=A_n/Q_n$ in lowest terms, $x_n=\{s_n\}$, $r_n=\sum_{k\ge1}((n+k)2^k)^{-1}\in(0,1/n)$, $\{2^n\ln2\}=\{x_n+r_n\}$ and $x_{n+1}=2x_n+\frac1{n+1}\bmod1$ (the BBP map, *P23-E* §5). For $y\in\mathbb Q/\mathbb Z$ and a prime $p$, $e_p(y)\ge0$ denotes the exponent of $p$ in the reduced denominator of $y$.

**Overloaded symbols.** A few letters change meaning between sections. Each meaning is fixed locally:

- $e(t)=e^{2\pi it}$ throughout; in §2, $e=v_2(n)$ is the $2$-adic exponent of $n=2^em$; in §4.2–§4.3, $e$ is Euler's number and $e_K$ its partial sums.
- $E=E(2)$ in §0–§1 and §5–§9; in Prop. 4.2, $E_N=D\cdot4^N-x_N^2$; in §4.2, $E_K=K!\,e_K$ (OEIS A000522).
- $R(n)=V(n)-\omega(n)$ (§0–§1) and $R_2(n)$ (§2) are arithmetic functions; $R_n$ in Theorem 3.6 is the summand of the BBP state supported on $2$ and the primes $\le\sqrt n$ (*P23-E* §5.3).
- $S_j$ is a column bit mass, $S_N(1;x)$ a Weyl sum, and $S$ in the proof of Lemma 1.3 a sum of independent variables.
- $c_j$ is a column carry (§1); $c_k$ is a series coefficient (§3.1, Cor. 4.4); $c\in\{\tau,a_+\}$ in Prop. 1.7.
- $x_n=\{s_n\}$ is a BBP state (§3); in Prop. 4.2, $x_N=\lfloor2^N\sqrt D\rfloor$.

**Evidence labels** (repository conventions, [`docs/research-objectives.md`](../../docs/research-objectives.md)):

- *Paper proof*: complete written proof in this note.
- *Finite certificate*: exact integer or rational computation verified by `scripts/phase25_classical.py`.
- *External input*: a published theorem cited without re-proof (§5).
- *Conditional*: proved here under a stated, unproved hypothesis.
- *Finite measurement*: finite digit or prefix statistics; bears on no asymptotic limit.
- *Model value*: an exact computation inside a comparison model (independent Poisson columns); **not evidence** about the constant.
- *Open*.

No cross-model review was used for this note. Any later cross-model review is not independent human peer review.

**Scope statement.** **Nothing in this note proves normality, simple normality, simple nonnormality, $D^+<1$, $D^->0$, or (non)membership in $K_2$ for $E$, $E_+$, $\ln 2$, $\sqrt2$, $\sqrt3$, $\phi$, $\pi$, $e$, $\zeta(3)$ or any other constant of the fixed roster `BC-01`…`BC-50`. No benchmark status changes.** The existing external base-2 disjunctivity evidence on `BC-37` is preserved unchanged. The results are structural theorems, sharp barriers and exact reformulations (standing objectives 3 and 4), plus finite measurements that are labelled as such.

---

## Summary of conclusions

| Track | Result | Evidence |
| --- | --- | --- |
| G1 | **Carry–orbit identity** (Lemma 1.1): the column carries of $E$ are $c_j=\lfloor Y_j\rfloor$ with $\{Y_j\}=\{2^{j-1}E\}$; exact Kummer form $\sum_{j\le N}d_j=\sum_{j\le N}S_j-\kappa_1(N)+c_{N+1}-c_1$; depth-$L$ local carries satisfy $c_j^{(L)}\le c_j\le c_j^{(L)}+\lceil c_{j+L}2^{-L}\rceil$ | Paper proof; finite certificate (all $j\le2^{17}$) |
| G1 | **Carry targets** (Prop. 1.2): simple normality of $E$ $\iff\kappa_1(N)/N\to C_{\rm true}-\frac12\in[0.839103,0.839116]$ (restating *P24-A* Thm 9.1); in the CC-49 comparison law the bit-level carry density is exactly $C_{\rm true}-p_*\in[0.846642,0.846666]$, above the target by $\frac12-p_*\in[0.0075391,0.0075498]$ | Paper proof + finite certificate; the model value is **not evidence** |
| G1 | **Mesoscopic collision theorem** (Thm 1.5): for every fixed $h$, collision pairs at distance $h$ among sources $\le N$ number $o(N)$; yet collision pairs in columns $\le N$ number $\ge(C_{\rm true}-1-o(1))N\ge0.3391N$. So **all column sharing in $E$ occurs between sources whose distance tends to infinity**, and every fixed-shift statistic of $\tau$ (Ingham, Topacogullari, the $r$-point shifted-divisor conjecture, fixed-shift mark laws) assigns density zero to each individual collision event | Paper proof (shifted Erdős–Kac for differences proved in Lemma 1.3) |
| G1 | **Fourier form of the missing input** (Prop. 1.6): collision counts are exact integrals of two-point correlations of the multiplicative family $e(\theta V(n))\chi(U(n))$; what is needed is a bivariate local law at shifts $h\le H(N)\to\infty$ with per-shift error $o(1/H)$, beyond fixed-shift and shift-averaged Elliott-type results | Paper proof (identity); requirement **Open** |
| G1/G2 | **Bounded-perturbation barrier** (Prop. 1.7): perturbing $\tau$ or $a_+$ by mean-zero integers in $[-3,3]$ preserves the mean, every fixed-shift correlation asymptotic (Ingham; *P24-E* Thm 3.3's unconditional $C_+(h;X)$) and the raw-tail variance, while the constant becomes $E+z$ or $E_++z$ for **any** $z\in[0,\frac14]$ (dyadic, hence in $K_2$, or normal) | Paper proof; finite certificate |
| G2 | **Sign–distance rule** (Lemma 2.1): $\operatorname{sign}(a_+(n)a_+(n+h))=(-1)^h$ whenever nonzero; a collision pair of $E_+$ reinforces iff its distance is even iff $\lambda_+(n)\lambda_+(n+h)(-1)^{i-i'}=1$ for the Liouville-type multiplicative function $\lambda_+=(-1)^{V_+}$ (Prop. 2.4) | Paper proof; finite certificate ($2{,}359{,}296$ pairs) |
| G2 | **Mesoscopic theorem for $E_+$** (Thm 2.2): $V_+=V+R_2$ with $R_2(n)=v_2(e-1)-v_2(e+1)$ for $n=2^em$, $e\ge2$; fixed-distance collisions have density zero; the bit mass per column is $<1$, so positivity of the collision density is **Open**; GF-40's unconditional two-point theorem does not constrain the digit law (Cor. 2.3) | Paper proof; finite certificate |
| G3 | **Dynamic rigidity** (Lemma 3.1, Thm 3.2, Prop. 3.4): sequences obeying the exact BBP recurrence are the shifted orbits $x_n+2^{n-n_1}\delta$; one exact denominator forces $\delta\in Q_{n_1}^{-1}\mathbb Z/\mathbb Z$, and exact denominators at all times force $\delta\in T=\prod_pT_p$; generalized band law at every $p$-adic level (Lemma 3.3); at $n_1=40$, $\lvert T\rvert=5{,}054{,}400$ exactly, against $\varphi(Q_{40})$ pointwise choices at **each** time | Paper proof; finite certificate ($327{,}254$ band-law pairs) |
| G3 | **Fixed-depth reduction** (Thm 3.5): every fixed-depth joint statistic of consecutive BBP states equals, asymptotically, a one-point statistic pushed forward by $(x,2x,\dots,2^Lx)$; the recurrence alone is satisfied by the shifted orbit of every real $y$ | Paper proof; finite certificate |
| G3 | **Geometric-reset barrier** (Thm 3.6): there are states with the **exact** denominators $Q_n$ at every $n$, the true components at every prime outside the top band of the last reset, and the exact BBP recurrence at every step except $O(\log N)$ resets $n_{i+1}=\lfloor\frac32n_i\rfloor$, yet $\|\tilde x_n\|\to0$ and $S_N\to1$. With $O(1)$ resets the class collapses to the finite rigidity class. **$D^+(\ln2;2)\le0.9999$ remains Open** | Paper proof (+ Rosser–Schoenfeld, Montgomery–Vaughan external); finite certificate (blocks $[240,360)$, $[360,540)$) |
| G4 | **Signed support versus transitions** (Lemma 4.1) and **block-doubling identity** $2^{N+1}x_Nt_N+t_N^2+E_{2N}=4^NE_N$ (Prop. 4.2): an $\Omega(\sqrt N)$ signed-complexity bound for $\sqrt2$ is equivalent to an $\Omega(\sqrt N)$ digit-change bound, and the squaring identity transfers block information only into products with the next block. No new lower bound | Paper proof; finite certificate; lower bound **Open** |
| G4 | **Band law for $e$** (Thm 4.3): for $\sqrt K<p\le K$, $m=\lfloor K/p\rfloor$: $p^m\sum_{k\le K}\frac1{k!}\equiv\frac{(-1)^m}{m!}\sum_{i\le K-mp}\frac1{i!}\pmod p$; the rigidity of Thm 3.2 transfers to $e$ (Cor. 4.4); the reset barrier does not transfer by the same argument, because the top-band modulus has only $o(n)$ bits and the excluded classes move with $K(n)$ (identified missing step) | Paper proof; finite certificate ($15{,}210$ pairs) |

### Agenda outcomes

| Brief item | Outcome |
| --- | --- |
| G1: new unconditional carry-density bounds for $E(2)$ crossing $C_{\rm true}-\frac12$ | **Not obtained.** No bound on $\kappa_1/N$ beyond the trivial $[C_{\rm true}-1,C_{\rm true}]$. Theorem 1.5 proves why fixed-shift correlation methods cannot produce one: they are blind to column sharing. The needed correlations are quantified in Prop. 1.6 and §1.4 |
| G2: higher signed correlations, local cancellations, joint arrivals for $E_+(2)$ | Exact sign–distance and parity rules (Lemma 2.1, Prop. 2.4); fixed-distance collisions vanish (Thm 2.2); bounded-perturbation barrier for the GF-40 two-point theorem (Cor. 2.3). Higher-order correlations: **Open** |
| G3: joint-state restrictions absent from GF-40's pointwise countermodels; fixed-depth barrier | **Obtained.** Global recurrence plus one exact denominator leaves a finite class (Thm 3.2); fixed depth gives nothing (Thm 3.5); $O(\log N)$ resets give nothing (Thm 3.6) |
| G4: NAF lower bounds beyond BBCP; carry-aware theorems for $e$, $\pi$, $\zeta(3)$ | The $\Omega(\sqrt N)$ signed bound is equivalent to an open digit-change problem (Lemma 4.1); a new exact band law for $e$ (Thm 4.3); for $\pi$, $\zeta(3)$ only the general rigidity transfers (§4.3) |

---

## 1. G1: the original Erdős–Borwein constant $E(2)$

### 1.1 Carries as orbit points

**Lemma 1.1 (carry–orbit identity; Paper proof; Finite certificate).** For $j\ge1$ put $Y_j=\sum_{j'\ge j}S_{j'}2^{j-1-j'}$ and $c_j=\lfloor Y_j\rfloor$. Then:

1. $\{Y_j\}=\{2^{j-1}E\}$, $c_1=\lfloor E\rfloor=1$, and $S_j+c_{j+1}=d_j+2c_j$ for every $j\ge1$.
2. With $\kappa_1(N)=\sum_{j=1}^Nc_j$: $\sum_{j\le N}d_j=\sum_{j\le N}S_j-\kappa_1(N)+c_{N+1}-c_1$, and $0\le c_{N+1}=O(\log^2N)$.
3. For $L\ge1$ let $W_j^{(L)}=\sum_{t<L}S_{j+t}2^{L-1-t}$ and $c_j^{(L)}=\lfloor W_j^{(L)}/2^L\rfloor$, the carry out of column $j$ when columns $j,\dots,j+L-1$ are added with zero incoming carry. Then $c_j=\lfloor(W_j^{(L)}+c_{j+L})/2^L\rfloor$, so $c_j^{(L)}\le c_j\le c_j^{(L)}+\lceil c_{j+L}2^{-L}\rceil$. In particular $\sum_{j\le N}c_j^{(L)}\le\kappa_1(N)$ for every $L$.

*Proof.* (1) $2^{j-1}E=\sum_{j'<j}S_{j'}2^{j-1-j'}+Y_j$ and the first sum is an integer. From $Y_j=\frac12(S_j+Y_{j+1})$ we get $2c_j+2\{Y_j\}=S_j+c_{j+1}+\{Y_{j+1}\}$. Under the convention that expansions do not end in $1^\infty$, $\{Y_j\}=\{2^{j-1}E\}=0.d_jd_{j+1}\ldots$ in binary, so $2\{Y_j\}=d_j+\{Y_{j+1}\}$; subtract. (This holds for every real number; the irrationality of $E$ (Erdős 1948) is not needed.) $Y_1=E=1.6066\ldots$ gives $c_1=1$. (2) Sum the column equations over $1\le j\le N$. Every bit index satisfies $V(n)+i\le\log_2\tau(n)\le1+\frac12\log_2n$ (as $\tau(n)\le2\sqrt n$), so column $j'$ receives bits only from $n\in[j',j'+1+\frac12\log_2(2j')]$, each source contributing at most $2+\frac12\log_2(2j')$ bits. Hence $S_{j'}\le\beta(j')=(2+\frac12\log_2 2j')(3+\frac12\log_22j')$ and $c_{N+1}\le Y_{N+1}\le\sum_{t\ge1}\beta(N+t)2^{-t}=O(\log^2N)$. (3) Induction on $L$ from the column equations. $\square$

$\kappa_1(N)$ differs from the prefix carry count of *P24-A* Theorem 2.2 by $O(\log^2N)$, so both have the same density. The script certifies $d_1,\dots,d_{2^{17}}$ and $c_1,\dots,c_{2^{17}+1}$ by monotone coupling of the unknown incoming carry at column $2^{17}+65$. That carry is bounded by the estimate of (2), evaluated in exact rational arithmetic as $Y<143.76<1000$ after replacing $\log_2(2j)$ by the bit length of $2j$; the floating-point value of the $\beta$-sum is about $132.01$. The script cross-checks the first $4096$ digits against an independent Horner evaluation, whose tail is at most $2\sqrt{4160}+4<400$ by an exact integer check, and verifies (1)–(3) at every $j\le2^{17}$ for $L\in\{1,2,4,8,16\}$.

*Finite measurement* ($N=2^{17}$; true $\kappa_1/N=0.82934$):

| $L$ | 1 | 2 | 4 | 8 | 16 |
| --- | --- | --- | --- | --- | --- |
| $\frac1N\sum c_j^{(L)}$ | 0.41928 | 0.62529 | 0.77543 | 0.82529 | 0.82934 |
| columns with $c_j^{(L)}\ne c_j$ | 53,737 | 26,745 | 7,066 | 531 | **0** |

At this scale depth-16 local carries reproduce every carry, in line with CC-49's minimal column truncation $D=16$. This is a finite observation, not a statement about the limit.

### 1.2 Carry targets

**Proposition 1.2 (Paper proof; Finite certificate; the model value in (2) is not evidence).**

1. $E$ is simply normal in base 2 if and only if $\kappa_1(N)/N\to C_{\rm true}-\frac12\in[0.839103,0.839116]$, and $\limsup f_1<\frac12$ if and only if $\liminf\kappa_1(N)/N>C_{\rm true}-\frac12$. Here $C_{\rm true}=\lim\frac1N\sum_{n\le N}s_2(\tau(n))\in[1.339103,1.339116]$ (*P24-A* A1.6).
2. In the comparison law $Q_\infty$ of CC-49, the **mark columns** $J_t=U_{t,1}+\dots+U_{t,K_t}$ ($t\ge1$) are independent and identically distributed, with $K_t\sim\mathrm{Poisson}(1)$ and marks $U_{t,a}$ drawn independently from the limiting law $\nu$ of $U(n)$. Unpacking each mark into its bits gives the **bit columns** $S_t=\sum_{r\ge0}\sum_{a\le K_{t+r}}\mathrm{bit}_r(U_{t+r,a})$, which are stationary but not independent. The expected bit-level carry per column equals $C_{\rm true}-p_*\in[0.846642,0.846666]$, where $p_*\in[0.492450290,0.492460864]$ is CC-49's model one-frequency. It exceeds the simple-normality target by exactly $\frac12-p_*\in[0.0075391,0.0075498]$.

*Proof.* (1) By Lemma 1.1(2), $f_1(N)=\frac1N\sum_{j\le N}S_j-\kappa_1(N)/N+O(\log^2N/N)$. Every bit of a source $n\le N$ lies in a column $\le n$, and sources $n>N$ reach columns $\le N$ only for $n\le N+1+\frac12\log_2(2N)$, so $\sum_{j\le N}S_j=\sum_{n\le N}s_2(\tau(n))+O(\log^2N)=C_{\rm true}N+o(N)$.

(2) *Mark level.* Put $Y_t^{(\mathrm{mark})}=\sum_{k\ge0}J_{t+k}2^{-1-k}$. Then $\mathbb EY_t^{(\mathrm{mark})}=\mu=\mathbb E_\nu U<\infty$, the law of $Y_t^{(\mathrm{mark})}$ does not depend on $t$, and $Y_1^{(\mathrm{mark})}=\sum_{d\ge1}J_d2^{-d}$ is CC-49's $X$. So the digit $d_t=\lfloor2\{Y_t^{(\mathrm{mark})}\}\rfloor$ has $\mathbb Ed_t=Q_\infty(X\bmod1\ge\frac12)=p_*$.

*Bit unpacking.* Put $Y_t^{(\mathrm{bit})}=\sum_{k\ge0}S_{t+k}2^{-1-k}$. A mark $U$ in mark column $t+k$ contributes $U2^{-1-k}=\sum_{r\ge0}\mathrm{bit}_r(U)2^{r-1-k}$ to $Y_t^{(\mathrm{mark})}$. Its bit $r$ sits in bit column $t+k-r$, so it contributes to $Y_t^{(\mathrm{bit})}$ exactly when $r\le k$, and then with the same weight $2^{r-1-k}$. Hence

```math
Y_t^{(\mathrm{mark})}-Y_t^{(\mathrm{bit})}=\sum_{k\ge0}\sum_{a\le K_{t+k}}\sum_{r>k}\mathrm{bit}_r(U_{t+k,a})\,2^{r-1-k}.
```

Every exponent $r-1-k$ is $\ge0$, so the right side is a nonnegative integer whenever it is finite. By Tonelli, its expectation is

```math
\mathbb EK\sum_{r\ge1}\Pr\nolimits_\nu(\mathrm{bit}_r(U)=1)\sum_{k=0}^{r-1}2^{r-1-k}=\sum_{r\ge1}(2^r-1)\Pr\nolimits_\nu(\mathrm{bit}_r(U)=1)=\mathbb E_\nu\bigl[U-s_2(U)\bigr]=\mu-C_{\rm true}<\infty .
```

So the difference is almost surely a finite nonnegative integer. Therefore $\{Y_t^{(\mathrm{bit})}\}=\{Y_t^{(\mathrm{mark})}\}$ almost surely, the bit columns produce the same digits $d_t$ (so $\mathbb Ed_t=p_*$), and the bit-level carries $c_t=\lfloor Y_t^{(\mathrm{bit})}\rfloor$ satisfy $0\le c_t\le Y_t^{(\mathrm{mark})}$, which has finite mean $\mu$.

*Expectations.* From $Y_t^{(\mathrm{bit})}=\frac12(S_t+Y_{t+1}^{(\mathrm{bit})})$ and $2\{Y_t^{(\mathrm{bit})}\}=d_t+\{Y_{t+1}^{(\mathrm{bit})}\}$ we get the column equations $S_t+c_{t+1}=d_t+2c_t$, exactly as in Lemma 1.1(1). The triple $(S_t,d_t,c_t)$ is a fixed function of the i.i.d. sequence $(K_s,(U_{s,a})_a)_{s\ge t}$, so its law does not depend on $t$, and each entry has finite mean. Taking expectations gives $\mathbb ES+\mathbb Ec=\mathbb Ed+2\mathbb Ec$, so $\mathbb Ec=\mathbb ES-\mathbb Ed$. Here $\mathbb ES_t=\mathbb EK\cdot\mathbb E_\nu s_2(U)=C_{\rm true}$, since $s_2(\tau(n))=s_2(U(n))$ and $s_2(U(n))$ is uniformly integrable by Lemma 1.4, and $\mathbb Ed=p_*$. The intervals are exact `Fraction` arithmetic on the certified endpoints, rounded outward. The exact endpoints of $\frac12-p_*$ are $0.007539136$ and $0.007549710$. $\square$

CC-49's sufficient criterion ($\limsup\mathbb E_I\Psi_{16}<0.4962723$ along one sequence of dyadic shells) is therefore a sufficient criterion for the shell carry density to exceed $C_{\rm true}-\frac12$ along that sequence. *Finite measurement:* $\kappa_1(N)/N=0.82934$ and $f_1=0.50923$ at $N=2^{17}$ (§1.6). P17 records certified prefix frequencies $0.500678$, $0.495743$, $0.494216$ at $2^{20},2^{22},2^{24}$. Neither these numbers nor the model value bear on the limit.

### 1.3 The mesoscopic collision theorem

**Lemma 1.3 (shifted Erdős–Kac for differences; Paper proof).** Fix $h\ge1$ and let $n$ be uniform in $\{1,\dots,N\}$. Then $(\omega(n+h)-\omega(n))/\sqrt{2\log\log N}$ converges in law to $\mathcal N(0,1)$. Consequently, for every fixed $d\in\mathbb Z$,

```math
\#\{n\le N:V(n+h)-V(n)=d\}=o(N),
```

and the same holds with $V$ replaced by $V_+(n)=v_2(\lvert a_+(n)\rvert)$, counting only those $n$ for which both $n$ and $n+h$ are $\not\equiv2\pmod4$.

*Proof.* Let $y=N^{1/\log\log N}$, $\mathcal P=\{p\text{ prime}:h<p\le y\}$, $\xi_p(n)=\mathbf 1_{p\mid n+h}-\mathbf 1_{p\mid n}$ and $\sigma_y^2=2\sum_{p\in\mathcal P}1/p$. By Mertens, $\sigma_y^2=2\log\log N-2\log\log\log N+O(1)$. Write $\omega(n+h)-\omega(n)=F+G+H$ with $F=\sum_{p\in\mathcal P}\xi_p$, $H$ the sum over $p\le h$ ($|H|\le2\pi(h)$) and $G$ the sum over $p>y$. Since $n+h\le2N$, $\mathbb E_N|G|\le2\sum_{y<p\le2N}1/p+4\pi(2N)/N=2\log\log\log N+O(1)$, so $(G+H)/\sigma_y\to0$ in $L^1$.

*Moments of $F$.* For fixed $k$, $\mathbb E_NF^k=\sum_{p_1,\dots,p_k\in\mathcal P}\mathbb E_N\prod_i\xi_{p_i}$. Each product is a function of $n$ modulo $m=\operatorname{rad}(p_1\cdots p_k)\le y^k$ bounded by $1$, so it differs from its average over $\mathbb Z/m\mathbb Z$ by at most $m/N$. Over $\mathbb Z/m\mathbb Z$ the $\xi_p$ are independent by CRT, with $\Pr(\xi_p=\pm1)=1/p$ (as $p\nmid h$). Hence $\mathbb E_NF^k=\mathbb ES^k+O(y^{2k}/N)$ with $S=\sum_{p\in\mathcal P}X_p$ for independent copies $X_p$, and $y^{2k}/N=N^{2k/\log\log N-1}\to0$. The cumulants satisfy $\kappa_2(S)=\sigma_y^2$ and $|\kappa_r(S)|\le C_r\sum_p1/p$ for $r\ge3$ (every moment of $X_p$ is $O(1/p)$), so $\kappa_r(S/\sigma_y)\to0$ for $r\ge3$ and $\mathbb E(S/\sigma_y)^k\to\mathbb EZ^k$. Thus $\mathbb E_N(F/\sigma_y)^k\to\mathbb EZ^k$ for all $k$. The normal law is determined by its moments, so $F/\sigma_y\Rightarrow\mathcal N(0,1)$, and Slutsky gives the claim with $\sigma_y\sim\sqrt{2\log\log N}$.

*Local vanishing.* $V=\omega+R$ with $\mathbb E_N|R(n)|+\mathbb E_N|R(n+h)|\le4\rho$, where $\rho=\sum_p\sum_{f\ge2}(1+\log_2(f+1))p^{-f}<\infty$. For $A>0$, with $\Delta=\omega(n+h)-\omega(n)$ and $\sigma=\sqrt{2\log\log N}$,

```math
\Pr\nolimits_N(V(n+h)-V(n)=d)\le\sup_t\Pr\nolimits_N\bigl(|\Delta/\sigma-t|\le A/\sigma\bigr)+\frac{4\rho}A .
```

By Pólya's theorem the distribution functions of $\Delta/\sigma$ converge to $\Phi$ uniformly, so for fixed $\eta>0$ the supremum is eventually at most $2\eta/\sqrt{2\pi}+o(1)$. Let $N\to\infty$, then $\eta\to0$, then $A\to\infty$. For $V_+$ use $V_+=V+R_2$ (Theorem 2.2(1)) with $\mathbb E|R_2|$ bounded. $\square$

**Lemma 1.4 (marks; Paper proof).**

1. $\sup_N\frac1N\sum_{n\le N}s_2(U(n))^4\le\prod_p\bigl(1+\sum_{f\ge2}|g(p^f)-g(p^{f-1})|p^{-f}\bigr)<\infty$, where $g(p^f)=s_2(\operatorname{odd}(f+1))^4$.
2. For every integer $K\ge1$, $\frac1N\#\{n\le N:U(n)\ge2^K\}\le\lambda/K$ with $\lambda=\sum_p\sum_{f\ge2}\log_2(f+1)p^{-f}$.

*Proof.* (1) $s_2$ is submultiplicative and $s_2(2^ab)=s_2(b)$, so $s_2(U(n))^4\le g(n)$ for the multiplicative $g$ with $g(p)=1$. Writing $g=1*h$ gives $h(p)=0$ and $\sum_{n\le N}g(n)=\sum_dh(d)\lfloor N/d\rfloor\le N\sum_d|h(d)|/d$, which equals the product; it converges because $|h(p^f)|\le2(f+1)^4$. (2) Markov's inequality with $\log_2U(n)\le\sum_{p^f\parallel n,f\ge2}\log_2(f+1)$. $\square$

**Theorem 1.5 (mesoscopic collisions; Paper proof; Finite certificate for (2)–(3) on $N\le2^{17}$).** Let $\Pi_h(N)$ be the number of collision pairs at distance $h$ whose smaller source is $\le N$.

1. For every fixed $h\ge1$, $\Pi_h(N)=o(N)$. Hence, for every fixed $H$, the columns that contain two bits from sources at distance $\le H$ have natural density $0$.
2. Every collision pair satisfies $h\le\log_2\tau(n+h)\le1+\frac12\log_2(n+h)$.
3. $\sum_{j\le N}\binom{S_j}2\ge(C_{\rm true}-1)N-o(N)\ge0.3391N-o(N)$. Consequently, for every fixed $H$, the number of collision pairs in columns $\le N$ at distance $>H$ is at least $(C_{\rm true}-1-o(1))N$.

*Proof.* (1) Fix $h$ and $K$. Pairs with $i,i'<K$ satisfy (0.1) with $d=h+i-i'$ in a fixed finite set, so by Lemma 1.3 they number at most $K^2\max_{|d-h|<K}\#\{n\le N:V(n+h)-V(n)=d\}=o(N)$. A pair with $i\ge K$ or $i'\ge K$ forces $U(n)\ge2^K$ or $U(n+h)\ge2^K$. Such pairs number at most $\sum_{n\le N}s_2(U(n))s_2(U(n+h))(\mathbf 1_{U(n)\ge2^K}+\mathbf 1_{U(n+h)\ge2^K})$, which by Hölder and Lemma 1.4 is $\le C\,N\,K^{-1/2}$. Let $N\to\infty$, then $K\to\infty$. (2) From (0.1), $h=V(n+h)+i'-V(n)-i\le V(n+h)+i'\le\log_2\tau(n+h)$. (3) $\binom S2\ge S-1$ for every integer $S\ge0$, and $\sum_{j\le N}S_j\ge\sum_{n\le N}s_2(\tau(n))=C_{\rm true}N+o(N)$. Pairs in columns $\le N$ have sources $\le N+O(\log N)$, so by (1) those at distance $\le H$ number $o(N)$. $\square$

**Interpretation (consequence of Theorem 1.5).** The column process of $E$ has positive collision density, and its collisions live entirely at source distances tending to infinity. By (2), every distance is at most $1+\frac12\log_2n$. Heuristically the distances are of order $\sqrt{\log\log n}$, the spread of $V(n+h)-V(n)$ (Lemma 1.3); this order is **not** proved. Every fixed-shift correlation asymptotic of $\tau$, and every limit law of the marks $(U(n+h))_{0\le h\le H}$ at fixed $H$, is blind to collisions: by (1) the collision events at each fixed distance have density $0$. This covers Ingham's theorem, Topacogullari's affine theorem, the conditional $r$-point singular series of *P23-E* §2.3, and the fixed-shift mark laws of *P23-E* §4.2, which are correct and nontrivial as laws of the marks. So any proof of any column statistic of $E$, including the carry density and CC-49's 16-column statistic, must control $(V,U)$ at pairs of arguments whose separation grows with $N$. This turns the heuristic of *P23-E* §4.3 and P17 §5 ("offsets $T\pm O(\sqrt T)$, $T=\log\log N$") into a theorem about which correlations are irrelevant.

### 1.4 Fourier form and what is missing

**Proposition 1.6 (Paper proof).** For $\theta\in\mathbb R$, an integer $K\ge1$ and a Dirichlet character $\chi$ modulo $2^K$ put $F_{\theta,\chi}(n)=e(\theta V(n))\chi(U(n))$, a multiplicative function of modulus $1$ with $F_{\theta,\chi}(p)=e(\theta)$ for every prime $p$. For $h\ge1$, $d\in\mathbb Z$ and odd residues $a,a'$ modulo $2^K$,

```math
\#\{n\le N:V(n+h)-V(n)=d,\ U(n)\equiv a,\ U(n+h)\equiv a'\}
=\int_0^1\frac{e(-\theta d)}{2^{2K-2}}\sum_{\chi,\chi'}\overline{\chi(a)}\,\overline{\chi'(a')}\sum_{n\le N}F_{\theta,\chi'}(n+h)\overline{F_{\theta,\bar\chi}(n)}\,d\theta .
```

Membership $i\in B(n)$ depends only on $U(n)\bmod2^{i+1}$, and every bit index of a source $n\le N+h$ satisfies $i+1\le K_N:=\lceil2+\frac12\log_2(N+h)\rceil$. So every $\Pi_h(N)$ is a finite combination of these two-point correlations with modulus $2^{K_N}$, which grows with $N$. At a fixed modulus $2^K$, the pairs with $i<K$ and $i'<K$ are such a combination, and the remaining pairs number $O(NK^{-1/2})$ uniformly in $N$ (proof of Theorem 1.5(1)).

*Proof.* Orthogonality of $e(\theta\,\cdot)$ on $[0,1]$ and of characters modulo $2^K$ on odd residues. Multiplicativity follows from additivity of $V$ and multiplicativity of $U$. $\square$

**What would be needed (Open; context only, no external result is used in a proof).** The collision intensity per source, $\frac1N\sum_{h\le H}\Pi_h(N)$ with $H\ge1+\frac12\log_2(2N)$, is at least $C_{\rm true}-1-o(1)>0.339$ by Theorem 1.5(2)–(3). It is trivially $O(\log N)$, and heuristically $O(1)$; an unconditional $O(1)$ bound is not proved here. By Theorem 1.5(1) the intensity is carried by $h$ in a range that must grow with $N$. Determining it to within $o(1)$ requires, uniformly for $h\le H(N)$, the correlations of Prop. 1.6 with error $o(N/H)$ per shift after integration in $\theta$. That includes the pretentious range $|\theta|\lesssim(\log\log N)^{-1/2}$, where the main term is a bivariate local limit law for $(V(n),V(n+h))$ at shifted arguments. Two known kinds of input fall short:

- Fixed-shift results, such as Tao's logarithmically averaged two-point Elliott theorem (2016) for non-pretentious functions, give $o(1)$ at each fixed $h$. By Theorem 1.5 that regime contributes nothing to the columns.
- Shift-averaged results (Matomäki–Radziwiłł–Tao 2015) bound $\sum_{h\le H}\bigl|\sum_{n\le N}F(n)\overline{F(n+h)}\bigr|$ by $o(HN)$ for $H\to\infty$, under non-pretentiousness hypotheses. That is $o(N)$ per shift on average, while $o(N/H)$ is required, and it does not cover the pretentious range.

GF-28 and CC-49 add that order $r\ge7$ (and $r\ge9$ at $D=16$) is needed. So the input that would decide the carry target is an **$r$-point ($r\ge7$), shift-uniform ($h\le H(N)\to\infty$), lattice-local (exact differences of $V$) correlation law for $(V,U\bmod2^K)$ with error $o(1)$ in collision intensity**. We know of no result of this kind.

### 1.5 The bounded-perturbation barrier

**Proposition 1.7 (Paper proof; Finite certificate).** Let $c\in\{\tau,a_+\}$ and $x_c=\sum_nc(n)2^{-n}$. Every $z\in[0,\frac14]$ has a base-4 expansion $z=\sum_{m\ge2}u_m4^{-m}$ with $u_m\in\{0,1,2,3\}$. Put $\varepsilon(1)=\varepsilon(2)=0$, $\varepsilon(2m-1)=u_m$ and $\varepsilon(2m)=-u_m$ for $m\ge2$, and $c^\sharp=c+\varepsilon$. Then:

1. $\sum_nc^\sharp(n)2^{-n}=x_c+z$, because $u_m2^{-(2m-1)}-u_m2^{-2m}=u_m4^{-m}$.
2. $\bigl|\sum_{n\le X}(c^\sharp(n)-c(n))\bigr|\le3$ for all $X$, so the mean is unchanged (it is $\ln2$ for $a_+$).
3. For every fixed $h\ge0$, $\sum_{n\le X}c^\sharp(n)c^\sharp(n+h)-\sum_{n\le X}c(n)c(n+h)$ is at most $6\sum_{n\le X+h}\tau(n)+9X=O(X\log X)$ in absolute value. So Ingham's asymptotic, *P24-E* Theorem 3.3's unconditional $C_+(h;X)\sim c_+(h)\log^2X$, and $\sum c^2\sim\kappa X\log^3X$ persist. Writing $T_n(c)=\sum_{k\ge1}c(n+k)2^{-k}$, we have $|T_n(\varepsilon)|\le3$, so the raw-tail moments of *P23-E* Theorem 3.1 change by $O(\log^{3/2}X)$ and keep their leading constants.
4. For $c=\tau$, $c^\sharp\ge0$, since $\tau(2m)\ge3$ for $m\ge2$.

Since $[x_c,x_c+\frac14]$ contains dyadic rationals ($D_N\to1$) and, for Lebesgue-almost every $z$, normal numbers, **no conclusion about the base-2 digits of $E$ or $E_+$ follows from hypotheses that are stable under such perturbations.** That includes all fixed-shift correlation asymptotics, raw-tail moments, and smallness of the coefficient mean (the "reduced mean implies reduced complexity" fallacy). *Proof.* (1)–(2) telescoping; (3) $|c^\sharp(n)c^\sharp(n+h)-c(n)c(n+h)|\le3|c(n)|+3|c(n+h)|+9$, and $|\mathbb E[T(c)T(\varepsilon)]|\le3(\mathbb ET(c)^2)^{1/2}$; (4) $\tau(2m)\ge3$ for $m\ge2$. $\square$

### 1.6 Finite measurements (bear on no limit)

Columns $j\le N$; "pairs" are collision pairs; $h$ is the source distance.

| $N$ | $\log\log N$ | $f_1$ | $\kappa_1/N$ | bit mass$/N$ | $\sum(S_j-1)_+/N$ | pairs$/N$ | $P(h=1)$ | $P(h\le2)$ | mean $h$ | max $h$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $2^{10}$ | 1.936 | 0.48340 | 0.85254 | 1.3359 | 0.5010 | 0.5938 | 0.6579 | 0.9359 | 1.408 | 4 |
| $2^{12}$ | 2.118 | 0.49219 | 0.84375 | 1.3362 | 0.5068 | 0.6116 | 0.5980 | 0.8954 | 1.522 | 4 |
| $2^{14}$ | 2.273 | 0.50867 | 0.82941 | 1.3381 | 0.5138 | 0.6301 | 0.5590 | 0.8642 | 1.600 | 5 |
| $2^{16}$ | 2.406 | 0.50923 | 0.82903 | 1.3383 | 0.5199 | 0.6419 | 0.5325 | 0.8433 | 1.658 | 5 |
| $2^{17}$ | 2.467 | 0.50923 | 0.82934 | 1.3386 | 0.5222 | 0.6484 | 0.5214 | 0.8332 | 1.685 | 5 |

Pair density per source at fixed distance, by the dyadic shell of the smaller source. The column headed $2^s$ is the shell $[2^{s-1},2^s)$, of size $2^{s-1}$:

| shell | $2^9$ | $2^{10}$ | $2^{11}$ | $2^{12}$ | $2^{13}$ | $2^{14}$ | $2^{15}$ | $2^{16}$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $h=1$ | 0.3555 | 0.3945 | 0.3701 | 0.3516 | 0.3528 | 0.3452 | 0.3423 | 0.3363 |
| $h=2$ | 0.1797 | 0.1777 | 0.1895 | 0.1865 | 0.1956 | 0.1957 | 0.2015 | 0.2022 |
| $h=3$ | 0.0352 | 0.0488 | 0.0547 | 0.0635 | 0.0767 | 0.0762 | 0.0825 | 0.0826 |

At accessible scales all collisions have $h\le5$, half have $h=1$, and the $h=1$ density is about $0.34$ per source. Theorem 1.5 says it tends to $0$. The slow drift of mass towards larger $h$ is consistent with that, at a $\log\log$ rate, but proves nothing. The law of $V(n+1)-V(n)$ on $n\le2^{17}$ ($0.243$ at $0$, $0.205/0.203$ at $\mp1$) is still far from flat. Here $\frac1N\sum|V-\omega|=0.3987$ (elementary bound $<2.22$; floating-point value $2.2101$), $\frac1N\sum s_2(U)^4=8.37$ (majorant $<131.9$; floating-point value $131.8016$), and the excess $\sum(S_j-1)_+/N\approx0.52$ exceeds the proved floor $C_{\rm true}-1=0.339$.

---

## 2. G2: the original plus Erdős–Borwein constant $E_+(2)$

### 2.1 Signed columns and the sign–distance rule

Sources are $n\not\equiv2\pmod4$ (where $a_+(n)\ne0$), with displacement $V_+(n)=v_2(|a_+(n)|)$, mark $W(n)=\operatorname{odd}(|a_+(n)|)$ and sign $\sigma(n)=+1$ for odd $n$ and $-1$ for $4\mid n$. Source $n$ deposits signed bits $\sigma(n)$ in the columns $n-V_+(n)-i$ for the bits $i$ of $W(n)$, so $E_+=\sum_j(\text{signed column sum})_j2^{-j}$. Collision pairs are defined as in §0 with $V_+$ in (0.1). In this section $e=v_2(n)$ denotes the $2$-adic exponent of a source $n=2^em$, $m$ odd.

**Lemma 2.1 (sign–distance rule; Paper proof; Finite certificate).** If $a_+(n)a_+(n+h)\ne0$ then $\operatorname{sign}(a_+(n)a_+(n+h))=(-1)^h$. Hence a collision pair is **reinforcing** (equal signs, so the two bits add in the column sum) if $h$ is even and **cancelling** (opposite signs) if $h$ is odd. In a column with three or more bits, a reinforcing pair can still be offset by a third bit of the opposite sign.

*Proof.* $a_+(k)>0$ for odd $k$, $a_+(k)<0$ for $4\mid k$, and $a_+(k)=0$ for $k\equiv2\pmod4$. If $h$ is odd, one argument is odd and the other is even and nonzero, so divisible by $4$. If $h$ is even, $n\equiv n+h\pmod2$: both odd (both $+$) or both even and nonzero, hence both $\equiv0\pmod4$ (both $-$). $\square$

The odd-$h$ half is *P23-E* Theorem 2.2(1). The script checks all $2{,}359{,}296$ nonzero pairs with $n\le2^{16}$, $h\le64$, and every collision pair up to $N=2^{17}$.

### 2.2 Fixed-distance collisions vanish

**Theorem 2.2 (Paper proof; Finite certificate).**

1. $V_+(n)=V(n)+R_2(n)$ with $R_2(n)=v_2(e-1)-v_2(e+1)$ for $n=2^em$, $e\ge2$, and $R_2(n)=0$ for odd $n$. On $n\equiv2\pmod4$, where $a_+(n)=0$ and $n$ is not a source, we set $R_2(n)=0$. The mean of $|R_2|$ over all $n$ is $\sum_{e\ge2}|v_2(e-1)-v_2(e+1)|2^{-e-1}=0.08825\ldots$, certified in $[0.0882543,0.0882544]$ by exact rational arithmetic (terms $e<100$ exactly; tail at most $\sum_{e\ge100}e\,2^{-e-1}=101\cdot2^{-100}$).
2. For every fixed $h\ge1$, collision pairs of $E_+$ at distance $h$ among sources $\le N$ number $o(N)$.
3. The bit mass per column of $E_+$ has density $\mu_{\rm pop}(|a_+|)\in[0.914156,0.919767]<1$ (*P24-E* Theorem 3.1(a)). So no pigeonhole lower bound on collisions exists, and **positivity of the collision density of $E_+$ is Open.**

*Proof.* (1) For $e\ge2$, $|a_+(n)|=(e-1)\tau(m)$ and $\tau(n)=(e+1)\tau(m)$. (2) The proof of Theorem 1.5(1) applies verbatim. First, $V_+=\omega+R+R_2$ with $R+R_2$ bounded in $L^1$ (Lemma 1.3). Second, $W(n)=\operatorname{odd}(e-1)\,U(m)$ for $e\ge2$ and $W(n)=U(m)$ for $e=0$, so $s_2(W(n))\le(1+\log_2(e+1))\,s_2(U(m))$ for every source. Summing over $e$ and odd $m\le N/2^e$ with Lemma 1.4(1) and $\sum_{e\ge0}(1+\log_2(e+1))^42^{-e}<\infty$ bounds the fourth moment of $s_2(W)$. Third, $\log_2W(n)\le\sum_{p^f\parallel n,\,f\ge2}\log_2(f+1)$, so Markov's inequality gives the tail bound of Lemma 1.4(2) for $W(n)\ge2^K$. (3) is quoted. $\square$

**Corollary 2.3 (status of GF-40's two-point theorem; Paper proof).** *P24-E* Theorem 3.3 makes $C_+(h;X)=\frac1X\sum_{n\le X}a_+(n)a_+(n+h)\sim\rho(h)\frac6{\pi^2}\sigma_{-1}(h)\log^2X$ unconditional. These are correlations of raw values at fixed shifts. By Theorem 2.2(2) such shifts carry no column collisions, and by Proposition 1.7 the asymptotics survive perturbations that make the constant $E_++z$ for any $z\in[0,\frac14]$. So the elimination of (H2) does not constrain the digit law of $E_+$.

### 2.3 The parity of a collision is a Liouville-type correlation

**Proposition 2.4 (Paper proof).** $\lambda_+(n)=(-1)^{V_+(n)}$ ($n\not\equiv2\bmod4$) is multiplicative, with $\lambda_+(p^f)=(-1)^{v_2(f+1)}$ for odd $p$ and $\lambda_+(2^e)=(-1)^{v_2(\lvert e-1\rvert)}$ ($e\ne1$; at $e=0$ this gives $\lambda_+(1)=1$). It agrees with the Liouville function on odd squarefree $n$. A collision pair $((n,i),(n+h,i'))$ is reinforcing if and only if $\lambda_+(n)\lambda_+(n+h)(-1)^{i-i'}=1$.

*Proof.* $a_+$ is multiplicative ($a_+=1*f$ with $f(d)=(-1)^{d-1}$ multiplicative), so $V_+$ is additive on coprime factors. By (0.1) for $V_+$, $h=V_+(n+h)-V_+(n)+i'-i$, so $h$ is even iff $V_+(n+h)-V_+(n)\equiv i-i'\pmod2$. Apply Lemma 2.1. $\square$

So the balance of signed carries in the columns of $E_+$ is a two-point correlation of a Liouville-type function, restricted to the lattice events $\{V_+(n+h)-V_+(n)=h+i-i'\}$, at shifts $h$ that must grow with $N$ (Theorem 2.2(2)). This is averaged-Chowla-type information localized on collision events, and it is **Open**. *P24-E*'s sufficient test for $E_+(2)$ ($\liminf\bar c_1^{\rm NAF}>0.579512$) asks for a signed carry deficit equal to $0.579512/0.919767>63\%$ of all deposited bits. By Theorem 2.2(2), none of that deficit can come from collisions at bounded distance.

### 2.4 Finite measurements (bear on no limit)

| $N$ | bit mass$/N$ | pairs$/N$ | $P(h=1)$ | $P(h\le2)$ | reinforcing$/N$ | cancelling$/N$ | reinforcing share |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $2^{10}$ | 0.9121 | 0.2393 | 0.7918 | 0.9918 | 0.0479 | 0.1914 | 0.2000 |
| $2^{12}$ | 0.9131 | 0.2441 | 0.7280 | 0.9650 | 0.0581 | 0.1860 | 0.2380 |
| $2^{14}$ | 0.9139 | 0.2507 | 0.6859 | 0.9391 | 0.0661 | 0.1846 | 0.2637 |
| $2^{16}$ | 0.9146 | 0.2569 | 0.6439 | 0.9084 | 0.0731 | 0.1839 | 0.2845 |
| $2^{17}$ | 0.9148 | 0.2601 | 0.6252 | 0.8937 | 0.0765 | 0.1836 | 0.2940 |

At $N=2^{17}$ the pairs by distance are $21316,9155,2740,870,13,0$ for $h=1,\dots,6$. Cancelling ($h$ odd) collisions dominate because $h=1$ dominates at accessible scales. If collision distances were equidistributed modulo $4$ and independent of residues, counting nonzero pairs per residue class of $h$ (densities $\frac34,\frac12,\frac12,\frac12$ for $h\equiv0,1,2,3$) would suggest a reinforcing share near $\frac{5/4}{9/4}=\frac59$. That is a heuristic, not evidence; whether the share converges is Open.

---

## 3. G3: $\ln 2$ — joint BBP states

### 3.1 Solution space and dynamic rigidity

Work more generally with $\alpha=\sum_{k\ge1}c_kb^{-k}$, $b\ge2$, $c_k\in\mathbb Q$, $r_n=\sum_{k>n}c_kb^{n-k}\to0$, $s_n=\sum_{k\le n}c_kb^{n-k}$, $x_n=\{s_n\}$, $q_n$ the reduced denominator of $x_n$. The recurrence is

```math
x_{n+1}\equiv b\,x_n+c_{n+1}\pmod1 . \tag{R}
```

**Lemma 3.1 (Paper proof; Finite certificate).** A sequence $(\tilde x_n)_{n\ge n_1}$ in $\mathbb R/\mathbb Z$ satisfies (R) for all $n\ge n_1$ if and only if $\tilde x_n=x_n+b^{n-n_1}\delta$ for a unique $\delta\in\mathbb R/\mathbb Z$. In that case $\tilde x_n\equiv b^ny-r_n$ with $y=\alpha+b^{-n_1}\hat\delta$ for any lift $\hat\delta$ of $\delta$. So (R) alone is satisfied by the shifted orbit of every real $y$.

*Proof.* $\tilde x_n-x_n$ satisfies $u_{n+1}=bu_n$ in $\mathbb R/\mathbb Z$; and $x_n\equiv b^n\alpha-r_n$. $\square$

**Theorem 3.2 (dynamic rigidity; Paper proof).** Let $(\tilde x_n)_{n\ge n_1}$ satisfy (R) for all $n\ge n_1$, with $\delta$ as in Lemma 3.1.

1. If the reduced denominator of $\tilde x_{n_1}$ divides $q_{n_1}$, then $\delta\in q_{n_1}^{-1}\mathbb Z/\mathbb Z$. There are at most $q_{n_1}$ such sequences: the shifted orbits of the rational translates $\alpha+b^{-n_1}j/q_{n_1}$.
2. If $\tilde x_n$ has reduced denominator exactly $q_n$ for every $n\ge n_1$, then $\delta\in T=\prod_{p\mid q_{n_1}}T_p$ (CRT), where

```math
T_p=\bigl\{\delta_p\in p^{-v_p(q_{n_1})}\mathbb Z/\mathbb Z:\ e_p(x_n+b^{n-n_1}\delta_p)=e_p(x_n)\ \text{for all }n\ge n_1\bigr\}.
```

3. In contrast, at a single time $n$ there are $\varphi(q_n)$ states with reduced denominator $q_n$. GF-40's Barrier 2 uses this pointwise freedom independently at every $n$.

*Proof.* (1) $\delta=\tilde x_{n_1}-x_{n_1}$ has denominator dividing $q_{n_1}$. (2) Decompose $\delta=\sum_p\delta_p$ into $p$-primary parts. For $q\ne p$, $b^{n-n_1}\delta_q$ is $p$-integral, so $e_p(x_n+b^{n-n_1}\delta)=e_p(x_n+b^{n-n_1}\delta_p)$, and the reduced denominator is $\prod_pp^{e_p}$. $\square$

### 3.2 Generalized band law and the local factors for $\ln 2$

**Lemma 3.3 (generalized band law; Paper proof; Finite certificate).** Let $n\ge2$, let $p\le n$ be an odd prime, $J=\lfloor\log_pn\rfloor$ and $m=\lfloor n/p^J\rfloor\in[1,p-1]$. Then, as $p$-adic integers,

```math
p^J s_n\equiv2^{\,n-m}s_m\pmod p .
```

Hence $v_p(Q_n)=J$ if $p\nmid A_m$, and $v_p(Q_n)<J$ if $p\mid A_m$. In particular, if the **drop set** $D(p)=\{1\le m<p:p\mid A_m\}$ is empty, then $v_p(Q_n)=\lfloor\log_pn\rfloor$ for every $n\ge p$. ($J=1$ is *P23-E* Theorem 5.3.)

*Proof.* The terms $k\le n$ with $v_p(k)=J$ are $k=ip^J$ with $1\le i\le m<p$. Terms with $v_p(k)<J$ contribute valuation $\ge1-J$. Iterating Fermat gives $2^{p^J}\equiv2\pmod p$, so $2^{-ip^J}\equiv2^{-i}$ and $p^J\sum_{i\le m}2^{n-ip^J}/(ip^J)\equiv2^n\sum_{i\le m}2^{-i}/i=2^{n-m}s_m$. Since $m<p$, $Q_m$ is prime to $p$, and $s_m$ is a $p$-unit times $A_m$. $\square$

The script verifies Lemma 3.3 (valuation and leading digit) for all $327{,}254$ pairs with $n\le2000$, with $1602$ drop events; $106$ of the $302$ odd primes below $2000$ have $D(p)=\emptyset$. Among primes $<100$, the nonempty drop sets occur at $5,17,19,29,41,47,53,59,67,71,79,89,97$, with $D(5)=\{2\}$ and $D(17)=\{11\}$.

**Proposition 3.4 (local factors for $\ln 2$; Paper proof; Finite certificate).** Take $\alpha=\ln2$, $b=2$, $c_k=1/k$, so $q_n=Q_n$. Let $J_1=v_p(Q_{n_1})$.

1. If $D(p)=\emptyset$, then $p^{-(J_1-1)}\mathbb Z/\mathbb Z\subseteq T_p$, and $T_p$ is determined by the finitely many $n\in[n_1,p^{J_1+1})$.
2. $T_2$ is determined by $n\in[n_1,n_1+v_2(Q_{n_1}))$, and $0\in T_p$ always.
3. $\lvert T\rvert\ge3^{\lfloor\log_3n_1\rfloor-1}\ge n_1/9$, so the class grows with $n_1$, but it is finite. At $n_1=40$: $T_2,T_3,T_5,T_7,T_{11},T_{13},T_{17},T_{19},T_{23},T_{29},T_{31},T_{37}$ have $4,9,1,5,3,8,1,1,6,1,13,15$ elements. Every factor is certified exactly, so $\lvert T\rvert=5{,}054{,}400$, against $Q_{40}=1{,}335{,}732{,}864{,}265{,}800$.
4. Every member of the class is $\tilde x_n=x_n+2^{n-n_1}\delta$ ($n\ge n_1$) with $\delta\in T$. Its Weyl sums are eventually periodic twists $\frac1N\sum_{n_1\le n<N}e(x_n)e(2^{n-n_1}\delta)$ of those of $\ln2$: the twist $n\mapsto e(2^{n-n_1}\delta)$ is periodic once $n\ge n_1+v_2(Q_{n_1})$, when the $2$-part of $\delta$ has been absorbed, but not from $n_1$ if $\delta_2\ne0$.

*Proof.* (1) By Lemma 3.3, $v_p(x_n)=-\lfloor\log_pn\rfloor\le-J_1<v_p(\delta_p)$ whenever $v_p(\delta_p)\ge1-J_1$, so the exponent is unchanged. For $n\ge p^{J_1+1}$, $e_p(x_n)>J_1\ge-v_p(\delta_p)$ for every admissible $\delta_p$, so no condition arises. (2) $2^{n-n_1}\delta_2\in\mathbb Z$ once $n-n_1\ge v_2(Q_{n_1})$. (3) $D(3)=\emptyset$ since $A_1=1$ and $A_2=5$. For the certificate: the script computes each $T_p$ on $[40,2000]$. This is exact for $p=2$, and for $D(p)=\emptyset$ with $p^{J_1+1}\le2000$ by (1)–(2). For the four primes with $D(p)\ne\emptyset$ the computed superset is $\{0\}$, which equals $T_p$ by (2). $\square$

### 3.3 Fixed depth gives nothing

**Theorem 3.5 (fixed-depth reduction; Paper proof; Finite certificate).** For $t\ge0$, $x_{n+t}\equiv2^tx_n+s_{n,t}$ with $0\le s_{n,t}=\sum_{k=1}^t2^{t-k}/(n+k)<2^t/(n+1)$; here $s_{n,0}=0$, and $s_{n,t}>0$ for $t\ge1$. Hence for every $L$ and every continuous $F$ on $(\mathbb R/\mathbb Z)^{L+1}$,

```math
\frac1N\sum_{n<N}\Bigl(F(x_n,x_{n+1},\dots,x_{n+L})-F(x_n,2x_n,\dots,2^Lx_n)\Bigr)\longrightarrow0 .
```

So the limit points of the $(L+1)$-window empirical measures are exactly $(\mathrm{id},T,\dots,T^L)_*\mu$, $T(x)=2x$, for $\mu$ ranging over the limit points of the one-point empirical measures of $(\{2^n\ln2\})$. By Lemma 3.1 the same holds for the recurrence-compatible sequence of any real $y$. So **no fixed-depth joint statistic of BBP states carries information beyond the doubling orbit of an arbitrary real.** In particular a dyadic $y$ gives $D_N\to1$ and a normal $y$ gives Lebesgue measure.

*Proof.* Iterate (R). $F$ is uniformly continuous and $\max_{t\le L}s_{n,t}\to0$; also $r_n\to0$. The script checks the exact identity and the bounds for $16\le n<1500$, $t\le8$. $\square$

### 3.4 The geometric-reset barrier

**Theorem 3.6 (Paper proof; External input: Rosser–Schoenfeld for $n>60000$ and Montgomery–Vaughan; Finite certificate).** Let $n_0\ge240$ and $n_{i+1}=\lfloor\frac32n_i\rfloor$. There are states $\tilde x_n\in\mathbb Q/\mathbb Z$ ($n\ge n_0$) such that:

1. $\tilde x_n$ has reduced denominator exactly $Q_n$ for every $n\ge n_0$;
2. on each block $[n_i,n_{i+1})$, $\tilde x_n=x_n+2^{n-n_i}\delta_i$ with denominator of $\delta_i$ dividing $M_i=\prod_{n_i/2<p\le n_i}p$. Hence $\tilde x_n$ and $x_n$ have the same $q$-primary components for every prime $q\notin(n_i/2,n_i]$. This includes the summand $R_n$ of $x_n$ supported on $2$ and the primes $q\le\sqrt n$ (*P23-E* §5.3; unrelated to $R(n)=V(n)-\omega(n)$ of §0), and the phases of all other large primes;
3. $\tilde x_{n+1}=2\tilde x_n+\frac1{n+1}\bmod1$ for every $n\ge n_0$ except possibly when $n+1$ is a reset time $n_i$ ($i\ge1$). Since $n_{i+1}\ge\frac32n_i-\frac12\ge1.497\,n_i$, at most $1.72\log_2(N/n_0)+1$ violations occur up to $N$;
4. $\|\tilde x_n\|\to0$, hence $\frac1N\sum_{n_0\le n<N}e(\tilde x_n)\to1$.

*Proof.* Fix $i$, write $n=n_i$, $L=n_{i+1}-n\le n/2$ and $\mathcal P=\{p:n/2<p\le n\}$. For $p\in\mathcal P$ and $n\le n'<n_{i+1}$: $p>n/2\ge\sqrt{3n/2}>\sqrt{n'}$ and $\lfloor n'/p\rfloor\in\{1,2\}$ (as $n'<3p$). Since $p\nmid A_1A_2=5$, Lemma 3.3 gives $v_p(Q_{n'})=1$, with $p$-component $2^{n'-1}$ (band 1) or $5\cdot2^{n'-3}$ (band 2) modulo $p$. For $\delta=a/M_i$, the $p$-component of $2^{n'-n}\delta$ is $2^{n'-n}\bar a_p/p$ with $\bar a_p\equiv a(M_i/p)^{-1}\pmod p$. So $x_{n'}+2^{n'-n}\delta$ keeps the denominator $Q_{n'}$ for all $n'$ in the block iff $\bar a_p\notin F_p=\{-2^{n-1},-5\cdot2^{n-3}\}\bmod p$ for every $p\in\mathcal P$. That is at most two excluded classes of $a$ modulo each $p$; all other primes are untouched.

*Sieve.* Let $\tau_i=-\{2^n\ln2\}$ and let $a_0$ be the integer nearest to $M_i\tau_i$. In an interval of $K=n^2$ consecutive integers around $a_0$, at most $\sum_{p\in\mathcal P}2(K/p+1)\le\frac{4K+2n}{\ln(n/2)}<K$ integers are excluded. This uses $\#\mathcal P\le n/\ln(n/2)$ (Montgomery–Vaughan) and $\sum_{p\in\mathcal P}1/p\le\frac2n\#\mathcal P$; the last inequality holds because $\ln(n/2)>4+2/n$ for $n\ge240$. Pick an admissible $a$ with $|a-a_0|\le n^2/2$, so $|a/M_i-\tau_i|\le(n^2+2)/(2M_i)$.

*Smallness.* With $y_i=\ln2+2^{-n}a/M_i$, for $n\le n'<n_{i+1}$ we have $\tilde x_{n'}=x_{n'}+2^{n'-n}a/M_i\equiv2^{n'}y_i-r_{n'}$, and $2^ny_i\equiv a/M_i-\tau_i$. So $\|\tilde x_{n'}\|\le2^{n/2}(n^2+2)/(2M_i)+1/n'$. Finally $\log_2M_i\ge0.55\,n$: this is exact for $240\le n\le60000$ (finite certificate, via bit lengths), and for $n>60000$ it follows from $\vartheta(n)-\vartheta(n/2)\ge n(1-1/\ln n-0.50812)\ge0.40\,n$ (Rosser–Schoenfeld). Hence $\|\tilde x_{n'}\|\le(n^2+2)2^{-0.05n-1}+1/n'\to0$. Items 1–3 hold by construction. $\square$

*Finite certificate.* Two explicit blocks are constructed and verified in exact rational arithmetic: $[240,360)$ with $22$ primes ($\log_2M=164.52\ldots$) and $[360,540)$ with $31$ primes ($\log_2M=249.30\ldots$). In both, the target residue $a_0$ itself is admissible, every $\tilde x_n$ has reduced denominator exactly $Q_n$, the recurrence holds inside each block and fails at $360$, at every $n$ of each block the change $\tilde x_n-x_n$ has denominator dividing $M$ (so only primes of the reset's top band change), and $\max n\|\tilde x_n\|=0.9945$ and $0.9963$. So $\|\tilde x_n\|$ is essentially $r_n<1/n$.

### 3.5 The dichotomy, and the stretch target

**Corollary 3.7 (Paper proof).** For the BBP states of $\ln 2$:

1. global recurrence plus one exact denominator leaves a finite class of rational translates (Theorem 3.2, Prop. 3.4); a barrier inside this class is a statement about eventually periodic twists of the Weyl sums of $\ln2$ itself;
2. exact denominators at all times, all components outside the reset's top band, and the recurrence except at $O(\log N)$ geometric resets impose no constraint (Theorem 3.6);
3. the recurrence alone, or with any fixed-depth joint statistic, imposes no constraint (Lemma 3.1, Theorem 3.5);
4. exact denominators and fixed-band phases without the recurrence impose no constraint (*P24-E* Barrier 2).

Consequently an argument for $D^+(\ln2;2)<1$ through BBP states must use the recurrence at infinitely many points of **every** geometric schedule $n_{i+1}=\lfloor\frac32n_i\rfloor$ ($n_0\ge240$). Otherwise apply Theorem 3.6 to a tail $(n_i)_{i\ge I}$ of that schedule that starts strictly after the finitely many used reset times, keeping $\tilde x_n=x_n$ for $n<n_I$. The starting index $n_I$ must itself be unused, since the switch from $x_{n_I-1}$ to $\tilde x_{n_I}$ is a violation of the recurrence at $n_I$. The genuine joint-state restriction is therefore the global coupling of the exact recurrence with the arithmetic of the states. Whether $o(\log N)$ but unbounded resets still allow a barrier is Open. **$D^+(\ln2;2)\le0.9999$ remains Open.**

---

## 4. G4: algebraic irrationals and other benchmark constants

### 4.1 $\sqrt2$, $\sqrt3$, $\phi$: where the squaring method stops

For a binary word $w=d_1\cdots d_N$ let $\sigma(w)$ be the minimum of $\#\{m:a_m\ne0\}$ over $\delta_1,\dots,\delta_{N+1}\in\{-1,0,1\}$ with $a_m=d_m+2\delta_m-\delta_{m+1}\in\{-1,0,1\}$ (free boundary), and $\chi(w)=\#\{1\le m<N:d_m\ne d_{m+1}\}$.

**Lemma 4.1 (Paper proof; Finite certificate).** $\chi(w)\le3\sigma(w)+1$ and $\sigma(w)\le\chi(w)$.

*Proof.* Lower bound. On a maximal zero run $[u,v]$ of $a$ we have $d_m=\delta_{m+1}-2\delta_m$. Here $\delta_m=1$ is impossible, $\delta_m=-1$ forces $\delta_{m+1}=-1$ and $d_m=1$, and $\delta_m=0$ gives $d_m=\delta_{m+1}\in\{0,1\}$ with $\delta_{m+1}=1$ only for $m=v$. So the digits on $[u,v]$ are $1\cdots1$, $0\cdots0$ or $0\cdots01$: at most one internal transition. There are at most $\sigma+1$ zero runs and at most $2\sigma$ pairs $(m,m+1)$ meeting a nonzero position. Upper bound. Take $\delta_m=-d_m$ for $1\le m\le N$ and $\delta_{N+1}=-d_N$. Then $a_m=d_{m+1}-d_m$ for $m<N$ and $a_N=0$, so exactly $\chi(w)$ of the $a_m$ are nonzero, and every $\delta_m\in\{0,-1\}$. (This is the run decomposition: a maximal run of ones $[u,v]$ is written as $2^{-(u-1)}-2^{-v}$.) $\square$

GF-32 Theorem 5.5(c) is the fixed-boundary form. For irrational $\alpha$ with binary digits $d_m$, let $\sigma_N(\alpha)$ be the minimum number of nonzero $a_m$, $1\le m\le N$, over all signed expansions $\alpha=A+\sum_{m\ge1}a_m2^{-m}$ with $A\in\mathbb Z$ and $a_m\in\{-1,0,1\}$. Every such expansion arises from carries $\delta_{m+1}=2^m\sum_{k>m}(a_k-d_k)2^{-k}$ and $\delta_1=\lfloor\alpha\rfloor-A$, which satisfy $a_m=d_m+2\delta_m-\delta_{m+1}$. The signed tail $2^m\sum_{k>m}a_k2^{-k}$ lies in $[-1,1]$ and the binary tail in $(0,1)$, so $\delta_m\in\{-1,0\}$. In particular $\delta_{N+1}=+1$ never occurs, and $\sigma(d_1\cdots d_N)\le\sigma_N(\alpha)$. Conversely, the witness of the upper bound has $\delta_m\in\{0,-1\}$, and the tail $0.d_{N+1}d_{N+2}\ldots+\delta_{N+1}\in(-1,1)$ has a signed expansion, so the witness extends to a signed expansion of $\alpha$. Hence $\frac13(\chi_N(\alpha)-1)\le\sigma_N(\alpha)\le\chi_N(\alpha)$ for every irrational $\alpha$, and **$\sigma_N(\sqrt2)\gg N^\delta$ is equivalent to $\chi_N(\sqrt2)\gg N^\delta$**. That is the open digit-change problem recorded as *P24-E* Open Question 2; the best proved bound is $\chi_N/\log N\to\infty$ (*P24-E* Theorem 2.3, via Ridout). The BBCP bound $s_2\gg\sqrt N$ counts nonzero digits and implies nothing for $\chi_N$.

**Proposition 4.2 (block-doubling identity; Paper proof; Finite certificate).** For nonsquare $D\ge2$ let $x_N=\lfloor2^N\sqrt D\rfloor$, $E_N=D\cdot4^N-x_N^2\ge1$ and $t_N=x_{2N}-2^Nx_N\in[0,2^N)$ (digits $N+1,\dots,2N$). Then

```math
2^{N+1}x_Nt_N+t_N^2+E_{2N}=4^NE_N ,
```

hence $w_\pm(E_N)\le w_\pm(x_N)w_\pm(t_N)+\frac12w_\pm(t_N)(w_\pm(t_N)+1)+w_\pm(E_{2N})$ and $|w_\pm(E_N)-w_\pm(x_N^2)|\le w_\pm(D)$.

*Proof.* Expand $x_{2N}^2=(2^Nx_N+t_N)^2$ and subtract $D\cdot16^N$; then use subadditivity and submultiplicativity of $w_\pm$. For the square, take a minimal signed expansion $t_N=\sum_{j=1}^w\varepsilon_j2^{m_j}$ with $w=w_\pm(t_N)$. Then $t_N^2=\sum_j2^{2m_j}+\sum_{i<j}\varepsilon_i\varepsilon_j2^{m_i+m_j+1}$, since each cross term $2\varepsilon_i\varepsilon_j2^{m_i+m_j}$ is a single signed power of $2$. This is a sum of $w+\binom w2=\frac12w(w+1)$ signed powers of $2$, so $w_\pm(t_N^2)\le\frac12w(w+1)$. The same argument gives $w_\pm(x_N^2)\le\frac12w_\pm(x_N)(w_\pm(x_N)+1)$. $\square$

*Interpretation (not a theorem).* The squaring identity converts information about block $[1,N]$ only into information about products with block $[N+1,2N]$. In ordinary weight the forced term $D4^N-E_N$ has $s_2\ge N-O(1)$, the borrow cascade behind BBCP. In signed weight the forced term has weight at most $w_\pm(D)+w_\pm(E_N)$, and $w_\pm(E_N)$ is itself controlled by the next block. A lower bound on $w_\pm(x_N)$ along this route needs a lower bound on the next block's signed complexity, which is the original problem one scale up. This refines the neutralization barrier of *P24-E* Theorem 2.3(b). **No new unconditional lower bound is claimed.** *Finite measurement* ($N=4096$): $\sigma/N=0.3250,0.3389,0.3396$ and $\chi/N=0.4854,0.5088,0.5039$ for $\sqrt2,\sqrt3,\phi$.

### 4.2 $e$: a band law for the exponential partial sums

Let $e_K=\sum_{k=0}^K\frac1{k!}=E_K/K!$ with $E_K=\sum_{i\le K}K!/i!$ (OEIS A000522; $E_K=\lfloor e\,K!\rfloor$ for $K\ge1$).

**Theorem 4.3 (band law for $e$; Paper proof; Finite certificate).** For every prime $p$ with $\sqrt K<p\le K$, let $m=\lfloor K/p\rfloor$ (so $1\le m<p$) and $i=K-mp$. Then

```math
p^m\,e_K\equiv\frac{(-1)^m}{m!}\,e_i\pmod p .
```

Hence $v_p(K!/\gcd(E_K,K!))=m$ if $p\nmid E_i$, and is $<m$ if $p\mid E_i$. For even $K\ge2$, $E_K$ is odd and $v_2(\operatorname{den}e_K)=v_2(K!)=K-s_2(K)$.

*Proof.* Terms $k<mp$ have $v_p(k!)\le m-1$. For $mp\le k\le K$, the multiples of $p$ up to $k$ contribute $p^m\,m!$. The non-multiples form $m$ complete residue blocks, each with product $\equiv(p-1)!\equiv-1$ (Wilson), plus the block $mp+1,\dots,k$ with product $\equiv(k-mp)!$. So $k!/p^m\equiv(-1)^mm!\,(k-mp)!$ and $p^m\sum_{k=mp}^K\frac1{k!}\equiv\frac{(-1)^m}{m!}\sum_{i'\le K-mp}\frac1{i'!}$. Since $i<p$, $i!$ is prime to $p$. For even $K\ge2$, $E_K=K\,E_{K-1}+1\equiv1\pmod2$, so $E_K$ is odd and $v_2(\operatorname{den}e_K)=v_2(K!)$. $\square$

For $\ln 2$ the leading $p$-adic digit along a band window is $2^{N-m}s_m$: indexed by the band and evolving by doubling. For $e$ it is $(-1)^me_i/m!$: indexed by the remainder $i=K-mp$, so along the window it runs through the truncated exponential series modulo $p$. The drop events $p\mid E_i$ start $(K,p)=(3,2),(7,5),(9,5),(12,5)$ (from $E_1=2$, $E_2=5$, $E_4=65$), with $262$ drops among the $15{,}210$ pairs checked ($K\le400$). Note that $E_2=A_2=5$: the prime $5$ is dropped by both constants, in band $m=2$ for $\ln2$ and at remainder $i=2$ for $e$.

**Corollary 4.4 (rigidity transfers to $e$; Paper proof).** Let $K(n)=\min\{K:K!\ge n^22^n\}$, $z_n=\{2^ne_{K(n)}\}$ and $c_{n+1}=2^{n+1}(e_{K(n+1)}-e_{K(n)})\in\mathbb Q$. Then $z_{n+1}\equiv2z_n+c_{n+1}$, and $\{2^ne\}=\{z_n+r'_n\}$ with $0<r'_n\le2^{n+1}/(K(n)+1)!\le2/n^2$. Theorem 3.2 therefore applies verbatim to $e$, and Theorem 4.3 describes the large-prime part of the denominators (for large $n$ the 2-part disappears because $v_2(K(n)!)<K(n)<n$). Theorem 3.6 does **not** transfer by the same argument, for two separate reasons.

- *Smallness fails (unconditional).* Since $K(n)\sim n\ln2/\ln n$, the prime number theorem gives, for the top-band modulus $M=\prod_{K(n)/2<p\le K(n)}p$, $\log_2M\sim K(n)/(2\ln2)\sim n/(2\ln n)=o(n)$. For $\ln2$, Theorem 3.6 has $\log_2M_i\ge0.55\,n$, which keeps $2^{n'-n_i}\delta_i$ small on a block of length $\le n/2$. For $e$, $2^L/M\to\infty$ on every block of length $L\ge cn$ with fixed $c>0$, even if no residue class had to be excluded. Even all primes up to $K(n)$ give only $\log_2\prod_{p\le K(n)}p\sim n/\ln n=o(n)$ bits.
- *The excluded classes move.* For a prime $p$ in the top band of $K(n')$ ($m=1$), Theorem 4.3 gives $pe_{K(n')}\equiv-e_{K(n')-p}\pmod p$. So the $p$-component of $z_{n'}$ is $-2^{n'}e_{K(n')-p}/p$ (when $p\nmid E_{K(n')-p}$). A twist $2^{n'-n_i}\delta$ with $p$-component $2^{n'-n_i}\bar a_p/p$ keeps the exact denominator iff $2^{n'-n_i}\bar a_p\not\equiv2^{n'}e_{K(n')-p}$, that is, iff $\bar a_p\not\equiv2^{n_i}e_{K(n')-p}\pmod p$. Unlike the fixed set $F_p$ of Theorem 3.6, this class depends on $K(n')$, which increases about $L\ln2/\ln n$ times on a block of length $L$. That is $\asymp K(n)$ times on a block of length $\asymp n$, and $\asymp K(n)/\ln K(n)$ times on a block of length $cn/\ln n$ with $c<\frac12$, where smallness could still hold. We have not proved that these classes are distinct. If they are, a prime $p\asymp K$ can have up to $\asymp K/\ln K$ excluded classes instead of $\le2$, and the sieve bound $\sum_p\#F_p(K'/p+1)<K'$ of Theorem 3.6 fails.

Overcoming both obstructions is the identified missing step (Open).

### 4.3 $\pi$, $\zeta(3)$ and other BBP-type constants

BBP-type series $\sum_kp(k)/(q(k)b^k)$ (for example $\pi$ in base $16$, or Broadhurst's binary formula for $\zeta(3)$) are of the form of §3.1. Lemma 3.1, Theorem 3.2 and the fixed-depth reduction of Theorem 3.5 hold verbatim whenever $c_k=O(1/k)$, since $s_{n,t}=O(b^t/n)$. The band laws and Theorem 3.6 require the large-prime structure of the denominators $q(k)$, such as $(8k+1)(8k+4)(8k+5)(8k+6)$ for $\pi$ or cubes for $\zeta(3)$ (the $p^3\parallel$ den barrier of GF-28). That is not developed here (identified missing step; Open).

---

## 5. External inputs and hypothesis verification

| Input | Statement used | Hypotheses checked |
| --- | --- | --- |
| Erdős (1948) | $E(2)$ is irrational | cited in Lemma 1.1(1) for context only; the proof holds for every real under the non-$1^\infty$ convention |
| Borel (1909) | Lebesgue-almost every real is normal in base $2$ | used only in the remark after Prop. 1.7 (a.e. $z\in[0,\frac14]$) |
| Ingham (1927); Ramanujan (1916) | $\sum_{n\le X}\tau(n)\tau(n+h)\sim\frac6{\pi^2}\sigma_{-1}(h)X\log^2X$ for fixed $h\ge1$; $\sum_{n\le X}\tau(n)^2\sim\pi^{-2}X\log^3X$ | Prop. 1.7(3) only notes that these asymptotics persist; the perturbation estimate itself is elementary |
| Mertens (1874) | $\sum_{p\le x}1/p=\log\log x+B+O(1/\log x)$ | used at $x=y=N^{1/\log\log N}\to\infty$ and $x=2N$ (Lemma 1.3) |
| Probability (classical) | the normal law is determined by its moments; Slutsky's lemma; Pólya's uniform convergence to a continuous limit | Lemma 1.3; moments of bounded independent summands |
| Rosser–Schoenfeld (1962) | $\vartheta(x)>x(1-1/\ln x)$ for $x\ge41$; $\vartheta(x)<1.01624x$ for $x>0$ | used only for $n>60000$ (Theorem 3.6); $240\le n\le60000$ is an exact computation |
| Montgomery–Vaughan (1973) | $\pi(x+y)-\pi(x)\le2y/\ln y$ for $y>1$ | used with $x=y=n/2\ge120$ (Theorem 3.6) |
| Repository certificates | $C_{\rm true}\in[1.339103,1.339116]$ (GF-36, `scripts/phase24_digit_mass.py`); $p_*\in[0.492450290,0.492460864]$ (CC-49, `scripts/phase17_erdos_borwein_bias.py`); $\mu_{\rm pop}(\lvert a_+\rvert)\in[0.914156,0.919767]$ (GF-40) | quoted as certified intervals; existence of the mean $C_{\rm true}$ is a paper proof in *P24-A* |
| Context only (no proof uses them) | Tao (2016); Matomäki–Radziwiłł–Tao (2015); Bailey–Borwein–Crandall–Pomerance (2004); Bugeaud (2012); Ridout (1957, via GF-40); Bailey–Crandall (2001) | — |

## 6. Prior art and attribution

- Kummer's carry identity (1852) and the column representation of $E$ come from repository Phases 14, 16, 17 and 24. Lemma 1.1's identification $c_j=\lfloor Y_j\rfloor$ is elementary.
- Lemma 1.3 is the standard sieve–moment proof of Erdős–Kac (Granville–Soundararajan 2007), applied to a difference of shifted arguments. We believe the statement is classical (Kubilius-model results for $(\omega(n),\omega(n+h))$) and include the short proof for completeness. *P24-A* §10 used the same fact as External input.
- Theorem 1.5, Proposition 1.6's use of the family $e(\theta V)\chi(U)$ (the objects of CC-49), Proposition 1.7, Theorem 2.2, Proposition 2.4, Theorems 3.2, 3.5 and 3.6, Proposition 3.4, Lemma 3.3 for $J\ge2$, Proposition 4.2 and Theorem 4.3 are, as far as we know, new in this repository. A literature search was not performed for Theorems 1.5, 3.6 and 4.3. Congruences for A000522 modulo primes are classical in related forms.
- Lemma 2.1's odd-$h$ half is *P23-E* Theorem 2.2(1). Lemma 4.1 is a free-boundary form of GF-32 Theorem 5.5(c).
- The BBP map is due to Bailey–Crandall (2001); Barrier 2 and the band law with $J=1$ are GF-40 and GF-35.

## 7. Standing objectives advanced

| Result | Objective (`docs/research-objectives.md`) |
| --- | --- |
| Lemma 1.1, Prop. 1.2 | 3 (exact carry form of the digit law; quantified target $C_{\rm true}-\frac12$ against the model $C_{\rm true}-p_*$); 2 (criterion/reduction only: an exact carry criterion for simple nonnormality of $E$, not a proof of it) |
| Theorem 1.5, Prop. 1.6 | 4 (fixed-shift correlation methods excluded for column statistics of $E$); 3 (positive collision density, mesoscopic localization) |
| Prop. 1.7 | 4 (excluded methods: all hypotheses stable under bounded mean-zero perturbations, including the reduced-mean fallacy) |
| Lemma 2.1, Theorem 2.2, Cor. 2.3, Prop. 2.4 | 4 (GF-40's unconditional two-point theorem shown digit-blind); 3 (exact parity structure of signed carries) |
| Theorems 3.2, 3.5, 3.6, Cor. 3.7 | 4 (sharp barrier dichotomy for BBP-state methods; identifies the needed global coupling); 3 (necessary condition/reduction only: what a proof of $D^+(\ln2;2)<1$ through BBP states must use) |
| Lemma 3.3, Prop. 3.4 | 3/4 (exact $p$-adic structure at all levels; exact size of the dynamic class) |
| Lemma 4.1, Prop. 4.2 | 4 (where the BBCP convolution method stops; equivalence with the digit-change problem) |
| Theorem 4.3, Cor. 4.4 | 3/4 (exact large-prime structure of $e$'s binary states; rigidity transfer; missing step for the barrier) |

## 8. Reproduction and exact finite tests

```sh
python -B scripts/phase25_classical.py
```

Standard library only; exits `0` with **6,049,844 assertions** in about 6–10 s on a desktop machine.

- **G1** `[exact]`: column process to $2^{17}+64$; digits and carries of $E$ certified for $j\le2^{17}$ by monotone coupling (incoming-carry bound $Y<143.76<1000$, an exact rational majorant with an exact tail bound); independent Horner check of $4096$ digits (tail $<400$ by an exact integer check); column equations, Kummer form at five $N$, window identity and depth-$L$ bounds ($L\le16$) at every $j\le2^{17}$; $\binom{S_j}2$ pair counts, the floor $\sum\binom{S_j}2\ge\sum S_j-N$, and $h\le\log_2\tau(n+h)$ for every collision pair; Prop. 1.2 intervals as exact fractions with outward rounding ($\frac12-p_*\in[0.0075391,0.0075498]$, exact endpoints $0.007539136$ and $0.007549710$); Prop. 1.7 identities, the range $[0,\frac14]$, $\tau(2m)\ge3$, $0\le\sum_{n\le X'}\varepsilon(n)\le3$ for every $X'\le2^{14}$, and correlation-change bounds $6\sum_{n\le X+h}|c(n)|+9X$ for $c\in\{\tau,a_+\}$, $h\le8$, $X=2^{14}$. `[float]` evaluations of the Lemma 1.3/1.4 constants (not certified). `[finite]` all tables of §1.6.
- **G2** `[exact]`: $a_+$ against the alternating divisor sum ($n\le3000$); Lemma 2.1 on $2{,}359{,}296$ pairs; $V_+-V=R_2$ for all $n\le131536$; reinforcing $\iff h$ even on every collision pair. `[encl]` $\mathbb E|R_2|\in[0.0882543,0.0882544]$. `[finite]` §2.4.
- **G3** `[exact]`: $s_n$ for $n\le2000$; Lemma 3.1; Lemma 3.3 on $327{,}254$ pairs; drop sets $D(p)$, $p<2000$; all twelve local factors $T_p$ at $n_1=40$ (for $p=2$ the script checks that $[n_1,n_1+v_2(Q_{n_1}))$ lies in the computed range) and $\lvert T\rvert=5{,}054{,}400$; Theorem 3.5 for $16\le n<1500$, $1\le t\le8$; $\lfloor\log_2\prod_{n/2<p\le n}p\rfloor\ge0.55n$ for $240\le n\le60000$; two reset blocks with exact denominators, changes supported on the top band at every $n$ of each block, internal recurrence, the violation at the reset, and $\|\tilde x_n\|\le2^{n-n_i}|\eta_i|+1/n$.
- **G4** `[exact]`: block-doubling identity and weight inequalities for $D\in\{2,3,5\}$, $N\le300$; Lemma 4.1 ($\chi\le3\sigma+1$, $\sigma\le\chi$) on every prefix $N\le4096$ of $\sqrt2,\sqrt3,\phi$; Theorem 4.3 on $15{,}210$ pairs ($K\le400$); $E_j=\lfloor e\,j!\rfloor$ for $j<60$ from a rational enclosure of $e$; $2$-adic valuation for even $K$.

No WSL or Lean build is involved; no Lean statement was changed.

## 9. Open questions

1. **Mesoscopic local law for $E$.** Prove a bivariate local limit theorem for $(V(n),V(n+h))$, uniform in $1\le h\le H(N)$ for some $H(N)\to\infty$, with error $o(1/\sqrt{\log\log N})$ per shift. With marks this would give the asymptotic collision intensity of $E$, the first column statistic beyond one-point laws.
2. **Collision distances.** Show that collision distances of $E$ are of order $\sqrt{\log\log N}$ (tightness after scaling) and identify their limit law.
3. **$E_+$.** Is the collision density of $E_+$ positive? Does the reinforcing share converge, and is the limit the smooth-distance heuristic $\frac59$?
4. **Resets for $\ln 2$.** Does a barrier in the sense of Theorem 3.6 exist with $o(\log N)$ but unbounded resets, or with resets at ratio $n_{i+1}/n_i\ge1+1/\ln 2$ (beyond the information $\log_2Q_n\approx1.44n$ available at a reset)?
5. **Twisted problem.** For $\delta\in T$, is $D^+(\ln2+2^{-n_1}\delta;2)<1$ equivalent in difficulty to $D^+(\ln2;2)<1$? Can one prove $\limsup|S_N|<1$ for some member of the finite class?
6. **$e$.** Adapt Theorem 3.6 to $e$, where the top-band modulus has only $o(n)$ bits and the top-band components move at every increment of $K(n)$ (Cor. 4.4); or prove that no such barrier exists.
7. **$\pi$, $\zeta(3)$.** Band laws for the BBP denominators of $\pi$ (base 16) and for Broadhurst's binary $\zeta(3)$ formula, and the corresponding reset barriers.
8. **Unchanged.** $\sigma_N(\sqrt2)\gg N^\delta$ (*P24-E* Open Question 2); $D^+(\ln2;2)\le0.9999$; simple normality and $D^\pm$ of $E(2)$ and $E_+(2)$.

## References

- D. H. Bailey, J. M. Borwein, R. E. Crandall and C. Pomerance, On the binary expansions of algebraic numbers, *J. Théor. Nombres Bordeaux* **16** (2004), 487–518.
- D. H. Bailey and R. E. Crandall, On the random character of fundamental constant expansions, *Experiment. Math.* **10** (2001), 175–190.
- É. Borel, Les probabilités dénombrables et leurs applications arithmétiques, *Rend. Circ. Mat. Palermo* **27** (1909), 247–271.
- Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts in Math. **193**, Cambridge Univ. Press, 2012.
- P. Erdős, On arithmetical properties of Lambert series, *J. Indian Math. Soc.* **12** (1948), 63–66.
- A. Granville and K. Soundararajan, Sieving and the Erdős–Kac theorem, in *Equidistribution in Number Theory, An Introduction*, NATO Sci. Ser. II **237**, Springer, 2007, 15–27.
- A. E. Ingham, Some asymptotic formulae in the theory of numbers, *J. London Math. Soc.* **2** (1927), 202–208.
- E. E. Kummer, Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen, *J. Reine Angew. Math.* **44** (1852), 93–146.
- K. Matomäki, M. Radziwiłł and T. Tao, An averaged form of Chowla's conjecture, *Algebra Number Theory* **9** (2015), 2167–2196.
- H. L. Montgomery and R. C. Vaughan, The large sieve, *Mathematika* **20** (1973), 119–134.
- S. Ramanujan, Some formulae in the analytic theory of numbers, *Messenger Math.* **45** (1916), 81–84.
- G. W. Reitwiesner, Binary arithmetic, in *Advances in Computers* **1**, Academic Press, 1960, 231–308.
- J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, *Illinois J. Math.* **6** (1962), 64–94.
- T. Tao, The logarithmically averaged Chowla and Elliott conjectures for two-point correlations, *Forum Math. Pi* **4** (2016), e8.
- B. Topacogullari, On a certain additive divisor problem (2017), arXiv:1512.05770.
- Repository: Phase 17 [erdos-borwein-bias.md](../phase17/erdos-borwein-bias.md) (`CC-49`); Phase 22 [classical-targets-and-recon.md](../phase22/classical-targets-and-recon.md) (`GF-28`); Phase 23 [classical-correlations-and-log2.md](../phase23/classical-correlations-and-log2.md) (`GF-35`), [binary-partition-and-carry-complexity.md](../phase23/binary-partition-and-carry-complexity.md) (`GF-32`); Phase 24 [dense-digit-mass-and-lambert.md](../phase24/dense-digit-mass-and-lambert.md) (`GF-36`), [classical-constants-and-joint-numerators.md](../phase24/classical-constants-and-joint-numerators.md) (`GF-40`).
