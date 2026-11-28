# Dense digit-mass transfer, generalized Erdős–Borwein constants, arithmetic Lambert families and signed transition complexity

Phase 24, Track A. Companion script: `scripts/phase24_digit_mass.py` (3,095,904 exact checks, about 90 s; `python -B scripts/phase24_digit_mass.py` exits with code 0). Every numerical constant used in a theorem is a **Finite certificate** computed with exact integers, `fractions.Fraction`, or integer arithmetic at scale $2^{-192}$ with outward rounding. Section 6 of the script and §11 below report **finite measurements only**. A finite digit prefix never proves an asymptotic statement, and none is used as one. This note has received one cross-model review (`notes/phase24/reviews/track-a-review.md`), and its findings are addressed here. Cross-model review is not independent human peer review.

## Results at a glance

| Item | Statement | Evidence |
| --- | --- | --- |
| A1.1 | Kummer's identity for two and for many summands in every base $b$. Subadditivity of $s_b$ and $w_b$, $s_b(ac)\le s_b(a)s_b(c)$, and the sharp bound $w_b(ac)\le\min\{s_b(a)w_b(c),\,2w_b(a)w_b(c)\}$. The inequality $w_b(ac)\le w_b(a)w_b(c)$ fails in every base $b\ge3$ (§1) | Paper proof; exhaustive Finite certificate |
| A1.2 | **Truncation and carry-tail transfer.** An exact prefix identity, with a floored carry-tail digit contribution of size $O(\log N)$ under polynomial coefficient growth. The brief's "+1" claim is false: for $E(8)$ at $N=35$ the prefix digit sum exceeds the coefficient mass by $2$. The growth hypothesis cannot be dropped (§2) | Paper proof; Finite certificate for the counterexample |
| A1.3 | Frequency criteria for $D^-$, a zero-run bound, a transition-window bound, and **radix descent** $D_{kN}(x;b)\le\frac{b^k-1}{k(b-1)}D_N(x;b^k)$ (§2) | Paper proof |
| A1.4 | **Elementary mean values.** The squarefull convolution lemma and the independent-exponent model, with $h(p^e)=1-v_2(e+1)$ and $\sum_n\lvert h(n)\rvert/n<1.90385$. No Tauberian input is needed (§3) | Paper proof; Finite certificate for $H$ |
| A1.5 | **$E(2^k)=\sum_n 1/(2^{kn}-1)$ for every $k\ge3$.** It satisfies $\limsup f_1\le C_{\rm true}/k\le 0.44638$ in base 2. It is simply nonnormal in every base $2^j$, with explicit $D^->0$ in base 2 and in base $2^k$, and $D^-(E(2^k);2)\to1$ (§4) | Paper proof; Finite certificate for the constants |
| A1.6 | $C=\prod_p\sum_{j\ge0}p/(p^{2^j}+1)\in[1.4035953,\,1.4035958]$, below $29/20$. The exact mean of $s_2(\tau(n))$ is $C_{\rm true}\in[1.339103,\,1.339116]$ (§4) | Finite certificate |
| A1.7 | **Base-$b$ barrier.** If $b$ is not a power of 2, the mean of $w_b(\tau(n))$ is $+\infty$. The transfer method then says nothing about $E(b^k)$ in base $b$ for any $k$. $E(16)$ in base 4 is proved; $E(9)$ in base 3, $E(25)$ in base 5 and $E(100)$ in base 10 remain open (§5) | Paper proof with External input (Senge–Straus) |
| A1.8 | **Base-$b$ families that do work.** Unitary $\sum b^{\omega(n)}b^{-kn}$ for $k\ge1$ ($b\ge4$) and $k\ge2$ ($b=3$). The $\tau_b$ families $\sum_n\tau_b(n)b^{-kn}=\sum_m\tau_{b-1}(m)/(b^{km}-1)$ have certified thresholds, for example $k\ge1$ in bases 7, 9, 10 and $k\ge2$ in base 3 (§5) | Paper proof; Finite certificate |
| A2.1 | Odd-divisor series $E_{\rm odd}(2^k)$ is simply nonnormal in base 2 for every $k\ge3$ (§6) | Paper proof; Finite certificate |
| A2.2 | **$\tau_r$ dichotomy.** The mean of $s_b(\tau_r(n))$ is bounded if and only if $r$ and $b$ are multiplicatively dependent. In base 2 the $\tau_4$ and $\tau_8$ series are simply nonnormal for $k\ge4$ and the $\tau_{16}$ series for $k\ge5$. The brief's $w_b$ refinement $r\in\{1,\dots,b-1\}b^m$ fails (§6) | Paper proof with External input (Senge–Straus); Finite certificate |
| A2.3 | Unitary $E^*(2^k)=\sum_m\mu^2(m)/(2^{km}-1)$ satisfies $\limsup f_1\le1/k$. It is simply nonnormal for $k\ge3$, and $k=2$ is the threshold case (§6, §10) | Paper proof |
| A2.4 | Cubic-character series $L_\pm(2^k)$ (moduli 7, 9, 13, and every cubic character with $W_\chi<1$) are not 2-normal in **base 2** for every $k\ge4$, with explicit $D^-$ (§8) | Paper proof; Finite certificate |
| A3.1 | **Signed transition-count transfer.** For signed series, $\limsup(f_{01}+f_{10})\le\frac2k\limsup\frac1X\sum_{n\le X}w_\pm(a(n))$ (§7) | Paper proof |
| A3.2 | **$E_+(2^k)=\sum 1/(2^{kn}+1)$ for every $k\ge4$** is not 2-normal in base 2 and not normal in any base $2^j$. Also $D^-(E_+(16);2)\ge0.0459$. Here $W_+\in[0.908174,0.908184]$, and $k=4$ is optimal for the method (§7) | Paper proof; Finite certificate |
| A4.1 | **$E(4)$ boundary.** The exact identity $f_1(N)=C_{\rm true}/2-\kappa(N)/N+o(1)$ holds. Simple normality in base 2 is equivalent to the carry density tending to $(C_{\rm true}-1)/2\in[0.169551,0.169558]$. Pure digit mass cannot reach $k=2$ (§9) | Paper proof |
| A4.2 | **$E^*(4)$ boundary.** $\limsup f_1\le1/2$ is proved, and simple normality is equivalent to $\kappa^*(N)=o(N)$. Positive upper density of $\omega$-collisions would prove simple nonnormality (§10) | Paper proof; Conditional; Heuristic |
| A4.3 | Prefix statistics of 18 constants (§11) | Finite measurements only |

### Status of the brief's proposals

| Proposal in the Phase 24 brief | Outcome |
| --- | --- |
| $\sum_n\lvert h(n)\rvert/n<\infty$ for $h=g*\mu$, $g(n)=\prod s_2(e+1)$, makes the mean value elementary | **Confirmed.** $h(p^e)=1-v_2(e+1)$ is supported on squarefull $n$, and $H<1.90385$ (Lemma 3.1, Corollary 3.3) |
| Beat $C\le29/20$ | **Confirmed.** $C<1.403596$, and the true mean $C_{\rm true}<1.33912$ is strictly smaller |
| The carry tail adds at most $+1$ to $s_b$ and $w_b$ | **False in general.** For $E(8)$ at $N=35$, $\lfloor\tau_N\rfloor=3$, and the prefix exceeds the coefficient mass by $2$. The correct bound on the digit contribution $s_b(\lfloor\tau_N\rfloor)$ is $(b-1)\ell_b(\tau_N)\le(b-1)(1+\log_b(1+\tau_N))=O(\log N)$ under polynomial coefficient growth (note that the unrounded tail $\tau_N$ itself can grow polynomially, e.g. $\sum_{j\ge1}(N+j)2^{-j}=N+2$ for $a(n)=n,b=2,k=1$). The digit contribution is at most $+1$ whenever $\tau_N<2$ (Theorem 2.2) |
| $w_b(ac)\le w_b(a)w_b(c)$, hence $w_b(\tau(n))\le\prod w_b(e+1)$ | **False for every $b\ge3$.** $w_b((b-1)^2)=2$, and $w_3(\tau(pq))=w_3(4)=2>1$ (Lemma 1.2(c)) |
| $E(b^2)$ is provably simply nonnormal in base $b$ for every $b\ge3$ (e.g. $E(9)_3$, $E(100)_{10}$) | **Not proved.** The method is provably vacuous unless $b$ is a power of 2 (Theorem 5.1). $E(16)$ in base 4 is proved. The others remain **Open** |
| $\tau_r$ dichotomy at $r=2^m$; $w_b$ variant $r\in\{1,\dots,b-1\}b^m$ | **Confirmed in corrected form** (Theorem 6.2). The $w_b$ variant fails |
| $E^*(4)$ sits exactly on the threshold; a positive density of collisions would break it | **Confirmed as a reduction** (Theorem 10.1). The positive density of collisions is **Open** (Conditional Proposition 10.2) |
| $E_+(2^k)$ is not normal for $k\ge4$ via NAF weight, with mean $\approx0.94$ | **Confirmed.** The majorant is $0.93641$ and the true mean $0.90818$. Here $k=4$ is the optimum of the method, because the bound is at least $1/2$ at $k=3$ (Theorem 7.2) |

## 0. Conventions

Fix an integer radix $b\ge2$. For real $x$ let $d_j(x;b)$, $j\ge1$, be the digits of $\{x\}$ in the expansion not ending in $(b-1)^\infty$. Then

```math
\lfloor b^Nx\rfloor=\lfloor x\rfloor b^N+\sum_{j=1}^Nd_j\,b^{N-j}\qquad(N\ge0).
```

The orbit is $\{b^nx\}$, $n\ge0$. The point $\{b^nx\}$ lies in the cylinder of the word $w$ of length $L$ exactly when $d_{n+1}\cdots d_{n+L}=w$. Write $F_N(I)=\#\{0\le n<N:\{b^nx\}\in I\}/N$. In base 2 put $f_1(N)=\#\{j\le N:d_j=1\}/N$, and let $\mathrm{tr}_N(x)=\#\{1\le j<N:d_j\ne d_{j+1}\}$ count the binary transitions. Then $F_N([1/4,3/4))$ is the frequency $f_{01}+f_{10}$, which is `transitionFrequency` in `NormalityChecker/BinaryDiscrepancy.lean`. The extreme discrepancy $D_N(x;b)$ and $D^\pm$ are as in `docs/research-objectives.md` (`radixDiscrepancy`).

For integers $a\ge0$ write $s_b(a)$ for the digit sum and $w_b(a)$ for the number of nonzero digits. In base 2, $s_2=w_2$. For $c\in\mathbb Z$ the **signed weight** $w_\pm(c)$ is the least number of terms in $c=\sum\varepsilon_i2^{m_i}$ with $\varepsilon_i=\pm1$ and $m_i\in\mathbb Z_{\ge0}$, the NAF weight. For $A\in\mathbb Z$ with two's-complement bits $A_0,A_1,\dots$, which are eventually constant, set $T(A)=\#\{i\ge0:A_i\ne A_{i+1}\}$. Finally $\tau_r(n)$ is the number of ordered factorizations $n=d_1\cdots d_r$, so $\tau_r(p^e)=\binom{e+r-1}{r-1}$. Also $\tau=\tau_2$, $\tau_{\rm odd}(n)$ is the number of odd divisors, $\omega(n)$ is the number of distinct prime factors, and $n=2^em$ with $m$ odd.

The constants are the Lambert series

```math
E(q)=\sum_{n\ge1}\frac1{q^n-1}=\sum_{n\ge1}\tau(n)q^{-n},\qquad
E_+(q)=\sum_{n\ge1}\frac1{q^n+1}=\sum_{n\ge1}a_+(n)q^{-n},\qquad
E^*(q)=\sum_{m\ge1}\frac{\mu^2(m)}{q^m-1}=\sum_{n\ge1}2^{\omega(n)}q^{-n},
```

where $a_+(n)=\sum_{d\mid n}(-1)^{d-1}=(1-e)\,\tau_{\rm odd}(n)$ (Lean: `erdosBorweinPlusCoeff_eq`, [GF-28](../../docs/results.md#gf-28)). Also $E_{\rm odd}(q)=\sum_{m\ \rm odd}1/(q^m-1)=\sum\tau_{\rm odd}(n)q^{-n}$. We use $q=b^k$ throughout. The integer $k$ is the **construction exponent**: in base $b$ the $n$-th coefficient enters at digit position $kn$.

## 1. Elementary digit inequalities (A1.1)

**Lemma 1.1 (Kummer, many summands; Paper proof).** Let $a_1,\dots,a_m\ge0$. Add them column by column in base $b$. With incoming carry $c_{-1}=0$, column $j$ has total $\sum_ia_{i,j}+c_{j-1}=r_j+bc_j$, where $0\le r_j<b$. Then $r_j$ is the $j$-th digit of $\sum_ia_i$, and

```math
\sum_{i=1}^ms_b(a_i)-s_b\Bigl(\sum_ia_i\Bigr)=(b-1)\sum_{j\ge0}c_j\ \ge0 .
```

For two summands the carries satisfy $c_j\in\{0,1\}$, and this is Kummer's identity $s_b(a+c)=s_b(a)+s_b(c)-(b-1)\kappa_b(a,c)$.

*Proof.* Telescoping gives $\sum_jr_jb^j=\sum_ia_i+\sum_jc_{j-1}b^j-\sum_jc_jb^{j+1}=\sum_ia_i$, so the $r_j$ are the digits of the sum. Summing the column equations over $j$ gives $\sum_is_b(a_i)+\sum_jc_{j-1}=s_b(\sum a_i)+b\sum_jc_j$, and $\sum_jc_{j-1}=\sum_jc_j$. ∎

**Lemma 1.2 (Paper proof).** For $a,c\ge0$ and $t\ge0$:

- (a) $s_b(a+c)\le s_b(a)+s_b(c)$, $s_b(ab^t)=s_b(a)$ and $s_b(ac)\le s_b(a)s_b(c)$.
- (b) $w_b(a+c)\le w_b(a)+w_b(c)$.
- (c) $w_b(ac)\le\min\{s_b(a)w_b(c),\,2w_b(a)w_b(c)\}$, with $w_2(ac)\le w_2(a)w_2(c)$. For every $b\ge3$ the inequality $w_b(ac)\le w_b(a)w_b(c)$ is **false**: $w_b((b-1)^2)=2$ since $(b-1)^2=(b-2)b+1$. In particular $w_3(\tau(pq))=w_3(4)=w_3(11_3)=2>w_3(\tau(p))w_3(\tau(q))=1$. The factor 2 in (c) is attained.
- (d) $w_\pm$ is subadditive and submultiplicative, $w_\pm(-c)=w_\pm(c)=w_\pm(2c)$, $w_\pm(c)\le s_2(\lvert c\rvert)$, and $w_\pm(c)\le\lfloor\log_2\lvert c\rvert\rfloor+1$ for $c\ne0$.

*Proof.* (a) Subadditivity is Lemma 1.1. For the product, $ac=\sum_jc_j\,ab^j$ is a sum of $s_b(c)$ shifted copies of $a$.

(b) Let $S_a,S_c$ be the supports of the digits and $\varepsilon_i\in\{0,1\}$ the carry into position $i$. If $i\notin S_a\cup S_c$, the digit of $a+c$ at $i$ is $\varepsilon_i$ and no carry leaves $i$. So the nonzero digits of $a+c$ lie in $S_a\cup S_c\cup Z$, where $Z=\{i\notin S_a\cup S_c:\varepsilon_i=1\}$. For $i\in Z$, let $j<i$ be maximal with $\varepsilon_j=0$. Then position $j$ produces a carry with no carry entering it, so $a_j+c_j\ge b$, which forces $a_j,c_j\ge1$. Hence $j\in S_a\cap S_c$. Distinct $i\in Z$ end distinct maximal carry runs, so $i\mapsto j$ is injective. Therefore $w_b(a+c)\le\lvert S_a\cup S_c\rvert+\lvert S_a\cap S_c\rvert=w_b(a)+w_b(c)$.

(c) $ac$ is a sum of $s_b(a)$ shifted copies of $c$; apply (b). Alternatively, $ac=\sum_{i,j}a_ic_jb^{i+j}$ with $a_ic_j<b^2$ has at most two nonzero digits per term.

(d) Concatenate or multiply representations. For $w_\pm(2c)\ge w_\pm(c)$, take a minimal representation of $2c$. Two terms with exponent $0$ either cancel or merge into one term $2^1$, so a minimal representation has at most one such term, and parity rules out exactly one. Hence every exponent is at least $1$; halve them. ∎

The defining recursion $w_\pm(0)=0$, $w_\pm(1)=1$, $w_\pm(2c)=w_\pm(c)$, and $w_\pm(c)=1+\min\{w_\pm(\frac{c-1}2),w_\pm(\frac{c+1}2)\}$ for odd $c\ge3$ follows from the same parity argument. The script checks that it agrees with the NAF algorithm for $\lvert c\rvert\le4096$.

**Lemma 1.3 (transition increments; Paper proof).** For every $A\in\mathbb Z$ and $m\ge0$, $\lvert T(A\pm2^m)-T(A)\rvert\le2$. Consequently $T(A+c)\le T(A)+2w_\pm(c)$ for all $A,c\in\mathbb Z$, and $T(c)\le2w_\pm(c)$.

*Proof.* Adding $2^m$ leaves the bits below $m$ unchanged. Let $j\ge m$ be minimal with $A_j=0$. If there is no such $j$, every bit from $m$ upward becomes $0$, and only the pair $(m-1,m)$ can change. If $j=m$, only bit $m$ flips (from 0 to 1), so only the pairs $(m-1,m)$ and $(m,m+1)$ can change. If $j>m$, bits $m,\dots,j-1$ flip from 1 to 0 and bit $j$ flips from 0 to 1. Pairs inside $\{m,\dots,j-1\}$ keep their status, the pair $(j-1,j)$ changes from $(1,0)$ to $(0,1)$ and so remains a transition, and only the pairs $(m-1,m)$ and $(j,j+1)$ can change. In every case at most two pairs change; when $m=0$ the pair $(m-1,m)$ is absent. Subtraction is the inverse operation. ∎

The script checks every $A\in[-2^{12},2^{12})$ and $m\le13$; the constant $2$ is attained. It also checks $T(A+c)\le T(A)+2w_\pm(c)$ on $\lvert A\rvert,\lvert c\rvert\le600$.

## 2. Truncation and carry-tail transfer (A1.2–A1.3)

Let $k\ge1$ and $a:\mathbb N\to\mathbb Z$ with $\sum_n\lvert a(n)\rvert b^{-kn}<\infty$, and put $x=\sum_{n\ge1}a(n)b^{-kn}$. For $N\ge0$ let $M=\lfloor N/k\rfloor$ and set

```math
A_N=\sum_{n\le M}a(n)\,b^{N-kn}\in\mathbb Z,\qquad
\tau_N=\sum_{n>M}a(n)\,b^{N-kn},\qquad
\Theta_M=\sum_{m\ge1}\lvert a(M+m)\rvert\,b^{-km}.
```

**Theorem 2.1 (exact prefix decomposition; Paper proof).** $\lfloor b^Nx\rfloor=A_N+\lfloor\tau_N\rfloor$ and $\lvert\tau_N\rvert\le b^{k-1}\Theta_M$.

*Proof.* $b^Nx=A_N+\tau_N$ with $A_N$ an integer. For $n=M+m$ the exponent is $N-kn=(N-kM)-km\le k-1-km$. ∎

**Theorem 2.2 (unsigned transfer; Paper proof).** Let $a(n)\ge0$. Then $\tau_N\ge0$, and for every $N$

```math
\sum_{j=1}^Nd_j(x;b)=\sum_{n\le M}s_b(a(n))+s_b(\lfloor\tau_N\rfloor)-s_b(\lfloor x\rfloor)-(b-1)\kappa(N),
```

where $\kappa(N)\ge0$ is the column-carry total of the addition of the $M+1$ integers $a(n)b^{N-kn}$ ($n\le M$) and $\lfloor\tau_N\rfloor$. In the same way,

```math
\#\{j\le N:d_j\ne0\}\le\sum_{n\le M}w_b(a(n))+w_b(\lfloor\tau_N\rfloor)-w_b(\lfloor x\rfloor).
```

The **carry tail** obeys $s_b(\lfloor\tau_N\rfloor)\le(b-1)\,\ell_b(\tau_N)$ and $w_b(\lfloor\tau_N\rfloor)\le\ell_b(\tau_N)$, where $\ell_b(t)$ is the number of base-$b$ digits of $\lfloor t\rfloor$: $\ell_b(t)=0$ for $t<1$ and $\lfloor\log_bt\rfloor+1$ otherwise. It contributes at most $+1$ to both sums exactly when $\lfloor\tau_N\rfloor=0$ or $\lfloor\tau_N\rfloor=b^r$ for some $r\ge0$, since $s_b(T)\le1$ holds only for $T\in\{0\}\cup\{b^r:r\ge0\}$. In particular $\tau_N<2$ suffices, because then $\lfloor\tau_N\rfloor\in\{0,1\}$; this sufficient condition is not necessary (for example $s_b(b)=w_b(b)=1$).

*Proof.* Split $\lfloor b^Nx\rfloor$ by the conventions of §0 and apply Theorem 2.1. Then use Lemma 1.1, $s_b(ab^t)=s_b(a)$ and Lemma 1.2(b). ∎

**The "+1" claim fails (Finite certificate).** For $E(8)$ ($b=2$, $k=3$, $a=\tau$) and $N=35$ we have $M=11$ and $\tau_{35}=\tau(12)/2+\tau(13)/16+\tau(14)/128+\cdots\in[3,4)$. The script finds $s_2(\lfloor2^{35}E(8)\rfloor)-\sum_{n\le11}s_2(\tau(n))=2$. Thus the prefix exceeds the coefficient mass by $2$. Over $N\le3000$, $s_2(\lfloor\tau_N\rfloor)$ reaches $4$ for $E(2)$, $E(4)$ and $E(8)$.

**Corollary 2.3 (asymptotic transfer; Paper proof).** Suppose

```math
\textbf{(H)}\qquad \log(1+\Theta_M)=o(M),
```

which holds whenever $\log(1+\lvert a(n)\rvert)=o(n)$ and in particular when $\lvert a(n)\rvert\le Cn^A$. Then the carry-tail digit contribution $s_b(\lfloor\tau_N\rfloor)$ (and $w_b(\lfloor\tau_N\rfloor)$) is $o(N)$, and it is $O(\log N)$ under polynomial growth. Consequently

```math
\limsup_{N\to\infty}\frac1N\sum_{j\le N}d_j\le\frac1k\limsup_{X\to\infty}\frac1X\sum_{n\le X}s_b(a(n)),\qquad
\limsup_{N\to\infty}\bigl(1-f_0(N)\bigr)\le\frac1k\limsup_{X\to\infty}\frac1X\sum_{n\le X}w_b(a(n)).
```

*Proof.* If $\log_b(1+\lvert a(n)\rvert)\le\varepsilon n$ for $n\ge n_\varepsilon$, then $\Theta_M\le O_\varepsilon(1)+b^{\varepsilon M}/(b^{k-\varepsilon}-1)$. Moreover $(1/N)\sum_{n\le M}s_b(a(n))\le(M/N)\cdot(1/M)\sum_{n\le M}s_b(a(n))$ with $M/N\le1/k$. For $a=\tau$, $\tau(n)\le2\sqrt n$ gives $\tau_N\le4\sqrt{M+1}$. ∎

**Example (H cannot be dropped).** Take $k\ge3$, or $k=2$ with $b\ge3$, and $a(n)=b^{\lfloor kn/2\rfloor}$. Then $s_b(a(n))=1$, but $x=\sum_nb^{-\lceil kn/2\rceil}$ has digit 1 at the strictly increasing positions $\lceil kn/2\rceil$ and $0$ elsewhere. This is the expansion of §0, because it does not end in $(b-1)^\infty$: for $k\ge3$ infinitely many positions are skipped, and for $k=2$, $b\ge3$ every digit is $1<b-1$. So the frequency of the digit 1, and the digit average, tend to $2/k$, which exceeds the bound $1/k$. The case $(b,k)=(2,2)$ must be excluded: there $x=\sum_n2^{-n}=1$, whose fractional digits are all $0$. Here $\log\Theta_M\asymp kM/2$.

**Proposition 2.4 (frequency criteria; Paper proof).** Let $\beta_s=\limsup\frac1N\sum_{j\le N}d_j$, $\beta_w=\limsup\#\{j\le N:d_j\ne0\}/N$, and in base 2 let $\beta_T=\limsup\mathrm{tr}_N/N$.

1. If $\beta_s<\frac{b-1}2$, then $x$ is not simply normal in base $b$, and $D^-(x;b)\ge\bigl(\frac{b-1}2-\beta_s\bigr)/(b-1)$.
2. If $\beta_w<\frac{b-1}b$, then $x$ is not simply normal in base $b$, and $D^-(x;b)\ge\frac{b-1}b-\beta_w$.
3. *(zero runs)* For every $m\ge1$, $D^-(x;b)\ge1-m\beta_w-b^{-m}$.
4. *(transition windows, base 2)* For every $m\ge2$, $D^-(x;2)\ge1-2^{1-m}-(m-1)\beta_T$. At $m=2$ this reads $D^-\ge\frac12-\beta_T$, and $\beta_T<\frac12$ implies that $x$ is not 2-normal in base 2.
5. *(radix descent)* For every $k\ge1$ and $N$, $D_{kN}(x;b)\le\frac{b^k-1}{k(b-1)}D_N(x;b^k)$. Hence $D^-(x;b^k)\ge\frac{k(b-1)}{b^k-1}D^-(x;b)$. Moreover, simple normality in base $b^k$ implies simple normality in base $b$, so simple nonnormality descends from base $b$ to every base $b^k$.

*Proof.* (1) $\frac1N\sum_{j\le N}d_j=\sum_{t=1}^{b-1}F_N([t/b,1))$, and each term is within $D_N$ of $(b-t)/b$.

(2) $F_N([1/b,1))$ is the frequency of nonzero digits.

(3) $\{b^nx\}\in[0,b^{-m})$ exactly when $d_{n+1}=\cdots=d_{n+m}=0$. A nonzero digit spoils at most $m$ starts, so $F_N([0,b^{-m}))\ge1-\frac mN\#\{j<N+m:d_j\ne0\}$.

(4) A window $d_{n+1}\cdots d_{n+m}$ is constant exactly when $\{2^nx\}\notin[2^{-m},1-2^{-m})$, which is a single interval of length $1-2^{1-m}$. A transition spoils at most $m-1$ windows.

(5) For $0\le n<kN$ write $n=kn'+r$ with $0\le r<k$. Then $\{b^nx\}\in I$ exactly when $\{b^{kn'}x\}$ lies in the preimage of $I$ under $y\mapsto\{b^ry\}$, a union of $b^r$ intervals of total length $\lvert I\rvert$. Summing the errors $b^rND_N(x;b^k)$ over $r$ gives the bound. Between consecutive multiples of $k$, $D$ changes by at most $2k/N'$. If the base-$b^k$ digits are uniform, each base-$b$ digit is uniform at each of the $k$ phases, because $b^{k-1}$ blocks carry a given digit at a given phase. ∎

## 3. Elementary mean values (A1.4)

**Lemma 3.1 (squarefull convolution; Paper proof).** Let $G$ be multiplicative and $h=G*\mu$, and assume $H:=\sum_n\lvert h(n)\rvert/n<\infty$. Then

```math
\frac1X\sum_{n\le X}G(n)\ \longrightarrow\ \sum_{n\ge1}\frac{h(n)}n=\prod_p\Bigl(1-\frac1p\Bigr)\sum_{e\ge0}\frac{G(p^e)}{p^e},
```

and $\sum_{n\le Y}G(n)\le HY$ for all $Y$ if $G\ge0$. The hypothesis holds when $G(p)=1$ for all but finitely many $p$ and $\lvert G(p^e)\rvert\le B(e+1)^A$, and then $H=\prod_p(1+\sum_{e\ge1}\lvert G(p^e)-G(p^{e-1})\rvert p^{-e})$.

*Proof.* $\sum_{n\le X}G(n)=\sum_{d\le X}h(d)\lfloor X/d\rfloor=X\sum_{d\le X}h(d)/d-\sum_{d\le X}h(d)\{X/d\}$. The last sum is at most $\sum_{d\le X}\lvert h(d)\rvert\le\sqrt X\,H+X\sum_{d>\sqrt X}\lvert h(d)\rvert/d=o(X)$. Absolute convergence gives the Euler product, using $\sum_e(G(p^e)-G(p^{e-1}))x^e=(1-x)\sum_eG(p^e)x^e$. Under the growth hypothesis, $\sum_p\sum_{e\ge2}\lvert\Delta G(p^e)\rvert p^{-e}\ll\sum_pp^{-2}$, and the finitely many primes with $G(p)\ne1$ contribute finitely. ∎

**Lemma 3.2 (independent-exponent model; Paper proof).** Let $F:\mathbb Z\to[0,\infty)$ be submultiplicative with $F(1)=1$, for example $w_\pm$ or $s_b$, where $s_b$ is extended to $\mathbb Z$ by $s_b(c):=s_b(\lvert c\rvert)$. For each prime let $u_p:\mathbb Z_{\ge0}\to\mathbb Z$ with $u_p(0)=1$, $u_p(1)=1$ for $p>p_0$, and put $\Phi(n)=F\bigl(\prod_pu_p(e_p(n))\bigr)$. Suppose the multiplicative majorant $G(n)=\prod_pF(u_p(e_p(n)))$ satisfies Lemma 3.1. Let $\varepsilon_p$ be independent with $\mathbb P(\varepsilon_p=e)=(1-1/p)p^{-e}$. Then almost surely only finitely many $u_p(\varepsilon_p)\ne1$, and

```math
\lim_{X\to\infty}\frac1X\sum_{n\le X}\Phi(n)=\mathbb E\,F\Bigl(\prod_pu_p(\varepsilon_p)\Bigr).
```

Writing $U_{\le y}=\prod_{p\le y}u_p(\varepsilon_p)$, for every $y$ the limit satisfies

```math
\mathbb E\,F(U_{\le y})\cdot\mathbb P\bigl(u_p(\varepsilon_p)=1\ \forall p>y\bigr)\ \le\ \lim\ \le\ \mathbb E\,F(U_{\le y})\cdot\prod_{p>y}\mathbb E\,F(u_p(\varepsilon_p)).
```

*Proof.* Fix $y>p_0$ and let $A_p=\{e:u_p(e)=1\}\ni0,1$. Call $n$ *good* if $e_p(n)\in A_p$ for every $p>y$; then $\Phi(n)=\Phi(n_y)$, where $n_y=\prod_{p\le y}p^{e_p(n)}$. Since $0\le\Phi\le G$ and $\sum_{n\le Y}G(n)\le HY$, the bad $n\le X$ contribute at most $HX\varepsilon_y$, where $\varepsilon_y=\sum_{p>y}\sum_{e\ge2}G(p^e)p^{-e}\to0$.

The good $n$ with $n_y=m$ are $n=mr$, where $r$ ranges over the support of the multiplicative indicator $\rho$ ($\rho(p^e)=0$ for $p\le y$ and $e\ge1$, and $\rho(p^e)=\mathbf 1_{A_p}(e)$ for $p>y$). Lemma 3.1 applies to $\rho$, so their number is $\delta X/m+o(X)$ with $\delta=\prod_{p\le y}(1-\frac1p)\prod_{p>y}\mathbb P(\varepsilon_p\in A_p)$. Truncating $e_p(m)\le E$ costs at most $HX\sum_{p\le y}\sum_{e>E}G(p^e)p^{-e}$, uniformly in $X$. Hence $\liminf$ and $\limsup$ of the mean lie in $[\mathbb EF(U_{\le y})\Pi_y,\ \mathbb EF(U_{\le y})\Pi_y+H\varepsilon_y]$, where $\Pi_y=\prod_{p>y}\mathbb P(\varepsilon_p\in A_p)\to1$.

Letting $y\to\infty$ shows that the limit exists. It equals $\mathbb EF(U)$ because $\mathbb E[F(U)\mathbf 1_{\rm bad}]\le\mathbb E[G\,\mathbf 1_{\rm bad}]\to0$ by Borel–Cantelli and the same majorant. For the displayed bounds, the lower one is the good event. The upper one is $F(U)\le F(U_{\le y})\prod_{p>y}F(u_p(\varepsilon_p))$ together with independence and Fatou. ∎

**Corollary 3.3 (Paper proof; Finite certificate for the numbers).** For $g(n)=\prod_{p^e\parallel n}s_2(e+1)$:

1. $s_2(m)-s_2(m-1)=1-v_2(m)$, so $h=g*\mu$ is multiplicative with $h(p^e)=1-v_2(e+1)$. It vanishes at primes, is supported on squarefull integers, and satisfies $\lvert h(p^e)\rvert\le\log_2(e+1)$.
2. $H=\sum_n\lvert h(n)\rvert/n=\prod_p(1+\sum_{e\ge2}\lvert1-v_2(e+1)\rvert p^{-e})\in[1.903838,\,1.903848]$.
3. The local identity

```math
\Bigl(1-\frac1p\Bigr)\sum_{e\ge0}\frac{s_2(e+1)}{p^e}=\sum_{e\ge0}\frac{1-v_2(e+1)}{p^e}=\sum_{j\ge0}\frac p{p^{2^j}+1}.
```

*Proof.* For (1), adding 1 to $m-1$ turns its $v_2(m)$ trailing ones into zeros and one zero into a one. For (3), $\sum_{m\ge1}s_2(m)x^m=\frac1{1-x}\sum_jx^{2^j}/(1+x^{2^j})$, because bit $j$ is set on $2^j$ consecutive residues modulo $2^{j+1}$. Put $x=1/p$ and divide by $x$. ∎

The script verifies the power-series form through $x^{2047}$ exactly and the support of $h$ for $n\le2\cdot10^5$; 768 values are nonzero, all at squarefull $n$. The weight $1-v_2$ in (1) is the same 2-adic weight that appears in $a_+(n)=(1-v_2(n))\tau_{\rm odd}(n)$.

## 4. Generalized Erdős–Borwein constants $E(2^k)$ (A1.5–A1.6)

**Theorem 4.1 (Paper proof; constants by Finite certificate).** The limit $C_{\rm true}=\lim_X\frac1X\sum_{n\le X}s_2(\tau(n))$ exists. It equals $\mathbb E\,s_2\bigl(\prod_p\operatorname{odd}(\varepsilon_p+1)\bigr)$ in the model of Lemma 3.2, and

```math
1.339103\le C_{\rm true}\le1.339116\ <\ 1.4035953\le C=\prod_p\sum_{j\ge0}\frac p{p^{2^j}+1}\le1.4035958\ <\ \frac{29}{20}.
```

For every $k\ge1$, $\limsup_Nf_1(N;E(2^k),2)\le C_{\rm true}/k$. For every $k\ge3$, therefore:

1. $\limsup f_1\le C_{\rm true}/3<0.44638<\frac12$. So $E(2^k)$ is not simply normal in base 2, and it is not simply normal in **any** base $2^j$, $j\ge1$, in particular its construction radix $2^k$. It is not normal.
2. $D^-(E(2^k);2)\ge\max\bigl\{\frac12-\frac{C_{\rm true}}k,\ \max_{m\ge1}\bigl(1-\frac{mC_{\rm true}}k-2^{-m}\bigr)\bigr\}$.
3. $D^-(E(2^k);2^j)\ge\frac j{2^j-1}D^-(E(2^k);2)$ for every $j\ge1$. Also $D^-(E(2^k);2^k)\ge\bigl(1-\frac{C_{\rm true}}2-\frac{k+1}{2^k}\bigr)/(k-1)$ for $k\ge4$.
4. $1-D^-(E(2^k);2)\le(C_{\rm true}\lceil\log_2k\rceil+1)/k$, so $\lim_{k\to\infty}D^-(E(2^k);2)=1$.

*Proof.* We have $\tau(n)=2^{\sum_pv_2(e_p+1)}\prod_p\operatorname{odd}(e_p+1)$, so $s_2(\tau(n))=s_2(\prod_p\operatorname{odd}(e_p+1))$. This has the form of Lemma 3.2 with $F=s_2$, $u_p(e)=\operatorname{odd}(e+1)$ and majorant $G=g$ from Corollary 3.3. Theorem 2.2 and Corollary 2.3 apply with $a=\tau\le2\sqrt n$.

Items (1)–(2) follow from Proposition 2.4(1)–(3) in base 2, where $\beta_s=\beta_w=\limsup f_1$. Item (3) uses Proposition 2.4(5). For the popcount bound, the mean popcount of the base-$2^k$ digits (aligned $k$-bit blocks) is at most $C_{\rm true}$ asymptotically, by Theorem 2.2 with $kN$ bits. So the digits of popcount at most 1 have lower frequency at least $1-C_{\rm true}/2$. They form $k-1$ runs of consecutive digits $\{0,1,2\},\{4\},\dots,\{2^{k-1}\}$ of total length $(k+1)/2^k$. Item (4) takes $m=\lceil\log_2k\rceil$ in Proposition 2.4(3). ∎

| $k$ | $\limsup f_1\le C_{\rm true}/k$ | $D^-(\cdot;2)\ge$ | $D^-(\cdot;2^k)\ge$ (descent) | $D^-(\cdot;2^k)\ge$ (popcount) |
| --- | --- | --- | --- | --- |
| 3 | 0.44638 | 0.05362 | 0.02298 | — |
| 4 | 0.33478 | 0.16522 | 0.04405 | 0.00598 |
| 5 | 0.26783 | 0.23217 | 0.03744 | 0.03573 |
| 6 | 0.22319 | 0.30362 | 0.02891 | 0.04421 |
| 8 | 0.16739 | 0.41522 | 0.01302 | 0.04218 |
| 10 | 0.13392 | 0.48217 | 0.00471 | 0.03552 |
| 16 | 0.08370 | 0.62391 | 0.00015 | 0.02201 |
| 64 | 0.02093 | 0.86413 | $2.9\cdot10^{-18}$ | 0.00524 |

All entries are computed from the certified upper end of $C_{\rm true}$ and rounded toward the weaker side. **$E(8)$ is simply nonnormal in its own construction radix 8**, where the construction exponent is 1. **$E(16)$ is simply nonnormal in base 4**. Since $C_{\rm true}\ge1$, the case $k=2$ is out of reach (§9).

*Certificate method.* The product $C$ is computed over $p\le3\cdot10^5$ in integer arithmetic at scale $2^{-192}$ with directed rounding. Each local factor is bracketed by a finite sum and an explicit geometric tail. For $p>Y$, $\ell(p)\le1+A/p^2$, and $\sum_{p>Y}p^{-2}$ is bounded exactly up to $4\cdot10^6$ plus $1/(3(Y_2-6))$, which covers $n\equiv\pm1\pmod6$. The bound $C_{\rm true}$ is a dynamic program over $p\le20000$. Its states are the values of $\prod_{p\le y}\operatorname{odd}(\varepsilon_p+1)$, with probability intervals; states below $2^{-64}$ are frozen with a majorant bound. The two bounds of Lemma 3.2 complete the computation.

## 5. Base $b\ge3$: barrier and working families (A1.7–A1.8)

**Theorem 5.1 (barrier; Paper proof with External input).** Let $b\ge2$ not be a power of 2. Then $\frac1X\sum_{n\le X}w_b(\tau(n))\to\infty$ and $\frac1X\sum_{n\le X}s_b(\tau(n))\to\infty$. Hence the bound of Corollary 2.3 is $+\infty$ for $E(b^k)$ in base $b$, for every $k$. For $b=2^j$, $E(b^k)=E(2^{jk})$ is simply nonnormal in base $b$ whenever $jk\ge3$, by Theorem 4.1. The method's threshold is therefore $k_0(2^j)=\lceil3/j\rceil$ (so $k_0(2)=3$, $k_0(4)=2$, $k_0(2^j)=1$ for $j\ge3$), and $k_0(b)=\infty$ when $b$ is not a power of 2. The same holds for $E_{\rm odd}(b^k)$, since $\tau_{\rm odd}(n)=2^{\omega(n)}$ for odd squarefree $n$.

*Remark (direct base-4 transfer at $k=1$).* For $E(4)$ in base 4 the threshold $k_0(4)=2$ is reached through base 2 and radix descent, and direct base-4 transfer does not reach $k=1$ either. Since $w_4(\tau(n))\ge1>\frac34$ for every $n$, Proposition 2.4(2) gives nothing. Proposition 2.4(1) would need the mean of $s_4(\tau(n))$ below $\frac32$. But $s_4(\tau(n))\ge2$ unless $\tau(n)$ is a power of 4. The indicator of the set of $n$ for which $\tau(n)$ is a power of 2 is multiplicative with value 1 at every prime, so by Lemma 3.1 this set has density $\delta_2=\prod_p(1-\frac1p)\sum_{i\ge0}p^{1-2^i}\le\frac12\sum_{i\ge0}2^{1-2^i}<0.8165$, since the other local factors are at most 1. On this set $\tau(n)=2^{t(n)}$, and $(-1)^{t(n)}$ extends by $0$ to a real multiplicative function with value $-1$ at every prime, whose mean is $0$ by Wirsing's theorem (External input). So the set of $n$ for which $\tau(n)$ is a power of 4 has density $\delta_2/2<0.4083$, and $\liminf_X\frac1X\sum_{n\le X}s_4(\tau(n))\ge2-\delta_2/2>1.59>\frac32$. The status of $E(4)$ in base 4 is open, as in base 2 (§9).
*Proof.* External input: Senge and Straus, *PV-numbers and sets of multiplicity*, Period. Math. Hungar. 3 (1973) 93–100. If $\log a/\log b$ is irrational, only finitely many integers have both $s_a$ and $s_b$ bounded; Stewart, J. reine angew. Math. 319 (1980) 63–72, gives an effective version. Since $s_2(2^r)=1$, it follows that $s_b(2^r)\to\infty$, and hence $w_b(2^r)\ge s_b(2^r)/(b-1)\to\infty$. Squarefree $n$ have $\tau(n)=2^{\omega(n)}$, and $\#\{n\le X:\omega(n)<r_0\}=o(X)$ for each fixed $r_0$. So the mean is at least $(6/\pi^2)c$ for every $c$. ∎

So for $E(9)$ in base 3, $E(25)$ in base 5 and $E(100)$ in base 10 the digit-mass method is **provably vacuous**, and their simple normality remains **Open**. The brief's numerical product $\prod_p(1-\frac1p)\sum_ew_3(e+1)p^{-e}\approx1.19$ is a correct Euler product but not an upper bound for the mean of $w_3(\tau(n))$, which is $+\infty$. *Heuristic (not evidence):* for $b$ not a power of 2, a typical $\tau(n)$ has about $(\log2/\log b)\log\log n$ base-$b$ digits. So the terms eventually overlap over unboundedly many blocks, and the digit statistics plausibly become uniform. This contrasts with the base-2 situation of Theorem 4.1. Finite prefixes, in which $\tau(n)$ is still short, look strongly nonuniform; see §11 for $E(100)$.

**Theorem 5.2 (base-$b$ families; Paper proof; thresholds by Finite certificate).**

1. *Unitary.* $E^*_b(b^k):=\sum_nb^{\omega(n)}b^{-kn}=\sum_m\mu^2(m)(b-1)^{\omega(m)}/(b^{km}-1)$ has base-$b$ digit average $\limsup\le1/k$. It is simply nonnormal in base $b$ when $1/k<(b-1)/2$, that is for every $k\ge1$ if $b\ge4$, for $k\ge2$ if $b=3$, and for $k\ge3$ if $b=2$. Then $D^-\ge(\frac{b-1}2-\frac1k)/(b-1)$. The cases $(b,k)=(2,2)$ and $(3,1)$ are threshold cases.
2. *$\tau_b$-families.* $\sum_n\tau_b(n)b^{-kn}=\sum_m\tau_{b-1}(m)/(b^{km}-1)$ has base-$b$ digit average $\limsup\le C_{[b]}/k$. Here $C_{[b]}=\mathbb E\,s_b(\prod_pu_b(\varepsilon_p))$, and $u_b(e)$ is $\binom{e+b-1}{b-1}$ with all factors $b$ removed; in particular $u_b(1)=1$. Its multiplicative majorant is $\prod_p(1-\frac1p)\sum_es_b(\binom{e+b-1}{b-1})p^{-e}$. The family is simply nonnormal in base $b$, and in every base $b^j$, for $k\ge k_0(b)$:

| $b$ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $C_{[b]}$ (true) | [1.5063, 1.5075] | [2.1606, 2.1638] | [2.0660, 2.0683] | [3.0703, 3.0770] | [2.7156, 2.7197] | [4.0048, 4.0165] | [3.2503, 3.2564] | [4.1996, 4.2150] |
| majorant $\le$ | 1.6024 | 2.7871 | 2.4551 | 5.3131 | 3.8789 | 9.2855 | 5.0760 | 10.8678 |
| $D^-$ at $k_0$, $\ge$ | 0.1231 | 0.1393 | 0.2414 | 0.1923 | 0.0467 | 0.2131 | 0.0929 | 0.0316 |
| $(b-1)/2$ | 1 | 1.5 | 2 | 2.5 | 3 | 3.5 | 4 | 4.5 |
| $k_0(b)$ | 2 | 2 | 2 | 2 | **1** | 2 | **1** | **1** |

*Proof.* (1) $s_b(b^{\omega(n)})=1$; apply Corollary 2.3 and Proposition 2.4(1). (2) $s_b(\tau_b(n))=s_b(\prod_pu_b(e_p))$, so Lemma 3.2 applies with $F=s_b$, because the majorant has $G(p)=s_b(b)=1$. The lower ends certify that the method fails at $k_0-1$. ∎

For example, $\sum_m\tau(m)/(9^m-1)=\sum_n\tau_3(n)9^{-n}$ is simply nonnormal in base 3, with $D^-\ge(1-0.7538)/2>0.123$. Also $\sum_m\tau_9(m)/(10^m-1)$ is simply nonnormal in base 10, with $D^-\ge(4.5-4.2150)/9>0.031$. These are the base-$b$ analogues of Erdős–Borwein that the method reaches. The square-divisor series $\sum_n\tau(n^2)3^{-kn}=\sum_m2^{\omega(m)}/(3^{km}-1)$ also has bounded base-3 mass, since $\tau(p^2)=3$. We have not computed its constant.

## 6. Arithmetic Lambert families in base 2 (A2.1–A2.3)

**Theorem 6.1 (odd divisors; Paper proof; Finite certificate).** $C_{\rm odd,true}=\lim\frac1X\sum s_2(\tau_{\rm odd}(n))\in[1.160633,\,1.160645]$, with majorant $\prod_{p>2}\sum_jp/(p^{2^j}+1)\in[1.177388,1.177389]$. Hence $E_{\rm odd}(2^k)$ is simply nonnormal in base 2 and in every base $2^j$ for every $k\ge3$; $\limsup f_1\le0.38689$ at $k=3$. At $k=2$ the method gives $C_{\rm odd,true}/2>\frac12$.

*Proof.* Lemma 3.2 with $u_2\equiv1$ and $u_p(e)=\operatorname{odd}(e+1)$ for odd $p$. ∎

**Theorem 6.2 ($\tau_r$ dichotomy; Paper proof with External input).** Let $r,b\ge2$.

1. If $r$ and $b$ are multiplicatively dependent, $r=t^v$ and $b=t^u$, then $\limsup\frac1X\sum_{n\le X}s_b(\tau_r(n))<\infty$.
2. If they are independent, $\frac1X\sum_{n\le X}w_b(\tau_r(n))\to\infty$.

In base 2 this reads: bounded if and only if $r=2^m$. With the certified true means

```math
C_{\tau_4}\in[1.55633,1.55674],\quad C_{\tau_8}\in[1.84104,1.84151],\quad C_{\tau_{16}}\in[2.00910,2.00962]
```

(majorants $1.62964$, $2.04316$, $2.30098$), the series $\sum_n\tau_r(n)2^{-kn}=\sum_m\tau_{r-1}(m)/(2^{km}-1)$ is simply nonnormal in base 2 for $k\ge4$ when $r=4,8$, and for $k\ge5$ when $r=16$. The method fails one step lower: $C_{\tau_4}/3,C_{\tau_8}/3>\frac12$ and $C_{\tau_{16}}/4>\frac12$.

*Proof.* (1) Since $b=t^u$, $s_b(m)\le(b-1)w_b(m)\le(b-1)w_t(m)\le(b-1)s_t(m)$: each nonzero base-$b$ digit contains a nonzero base-$t$ digit. Moreover $s_t(\tau_r(n))\le\prod_ps_t(\tau_r(p^{e_p}))$ with $s_t(\tau_r(p))=s_t(t^v)=1$, so Lemma 3.1 applies. (2) For squarefree $n$, $\tau_r(n)=r^{\omega(n)}$, and Senge–Straus gives $s_b(r^j)\to\infty$ because $s_r(r^j)=1$; argue as in Theorem 5.1. The thresholds follow from Lemma 3.2 with $u(e)=\operatorname{odd}\binom{e+r-1}{r-1}$. ∎

Theorem 5.1 is the case $r=2$. The brief's $w_b$ variant ("$r\in\{1,\dots,b-1\}\cdot b^m$") fails. For $r=db^m$ with $1<d<b$ multiplicatively independent of $b$, $w_b(r^j)=w_b(d^j)\to\infty$ by the same input. The square-divisor function $\tau(n^2)=\prod(2e+1)$ has value $3$ at primes, so its base-2 mass mean is $+\infty$; in base 3 it is bounded (§5).

**Theorem 6.3 (unitary; Paper proof).** $s_2(2^{\omega(n)})=1$, so $E^*(2^k)$ has $\limsup f_1\le1/k$. For $k\ge3$ it is simply nonnormal in every base $2^j$, with $D^-(E^*(2^k);2)\ge\max\{\frac12-\frac1k,\max_m(1-\frac mk-2^{-m})\}$. This bound is $\frac16$ at $k=3$, $\frac14$ at $k=4$ and $\frac12$ at $k=8$, and it tends to 1. The case $k=2$ is the exact threshold (§10).

## 7. Signed transition-count transfer and $E_+(2^k)$ (A3)

**Theorem 7.1 (Paper proof).** Let $a:\mathbb N\to\mathbb Z$ satisfy **(H)** and put $x=\sum a(n)2^{-kn}$, a real number of any sign. Then for every $N$

```math
\mathrm{tr}_N(x)\le T(\lfloor2^Nx\rfloor)\le2\sum_{n\le N/k}w_\pm(a(n))+2w_\pm(\lfloor\tau_N\rfloor),
\qquad
\limsup_{N}\bigl(f_{01}+f_{10}\bigr)(N)\le\frac2k\,\limsup_X\frac1X\sum_{n\le X}w_\pm(a(n))=:\frac{2W}k .
```

If $2W/k<\frac12$, then $x$ is not 2-normal in base 2 and not normal in any base $2^j$. Moreover $D^-(x;2)\ge\max_{m\ge2}\bigl(1-2^{1-m}-(m-1)\frac{2W}k\bigr)\ge\frac12-\frac{2W}k$, and $D^-(x;2^j)\ge\frac j{2^j-1}D^-(x;2)$.

*Proof.* The low $N$ bits of $\lfloor2^Nx\rfloor$ in two's complement are $d_N,\dots,d_1$ for every real $x$, so the transitions among $d_1,\dots,d_N$ are counted by $T$. Starting from $T(0)=0$, add each term $a(n)2^{N-kn}$ as $w_\pm(a(n))$ signed powers of 2, then add $\lfloor\tau_N\rfloor$; apply Lemma 1.3. Here $w_\pm(\lfloor\tau_N\rfloor)\le\log_2(\lvert\tau_N\rvert+2)+1=o(N)$ by **(H)**. Finish with Proposition 2.4(4)–(5). ∎

**Theorem 7.2 ($E_+(2^k)$; Paper proof; Finite certificate).** The mean $W_+=\lim\frac1X\sum_{n\le X}w_\pm(a_+(n))$ exists and

```math
0.908174\le W_+\le0.908184,\qquad W_+\le W_+^{\rm maj}=\frac12\sum_{e\ge0}\frac{w_\pm(\lvert1-e\rvert)}{2^e}\prod_{p>2}\Bigl(1-\frac1p\Bigr)\sum_{f\ge0}\frac{w_\pm(f+1)}{p^f}\in[0.936414,\,0.936415].
```

Hence for every $k\ge4$, $E_+(2^k)=\sum_n1/(2^{kn}+1)$ is not 2-normal in base 2 and not normal in any base $2^j$. Its $D^-$ is explicit:

| $k$ | 4 | 5 | 6 | 8 | 16 |
| --- | --- | --- | --- | --- | --- |
| $\limsup(f_{01}+f_{10})\le$ | 0.45410 | 0.36328 | 0.30273 | 0.22705 | 0.11353 |
| $D^-(E_+(2^k);2)\ge$ | 0.04590 | 0.13672 | 0.19727 | 0.29590 | 0.53443 |

Also $D^-(E_+(2^k);2)\to1$. **$k=4$ is optimal for the method.** Since $w_\pm(c)\ge1$ for $c\ne0$ and $a_+(n)\ne0$ exactly when $n\not\equiv2\pmod4$, $W_+\ge\frac34$. So $2W_+/3\ge\frac12$, and no bound of this kind reaches $E_+(8)$, $E_+(4)$ or $E_+(2)$.

*Proof.* $w_\pm(a_+(n))=w_\pm\bigl(u_2(e)\prod_{p>2}\operatorname{odd}(e_p+1)\bigr)$, with $u_2(e)=\operatorname{odd}(\lvert1-e\rvert)$ for $e\ne1$ and $u_2(1)=0$. This uses $w_\pm(\pm2^sc)=w_\pm(c)$. Lemma 3.2 applies with $F=w_\pm$ and majorant $G(2^e)=w_\pm(1-e)$, $G(p^f)=w_\pm(f+1)$. The value $G(2)=0$ affects only one prime. The coefficients satisfy $\lvert a_+(n)\rvert\le\tau(n)\le2\sqrt n$. ∎

The halving the brief anticipated is real. The 2-adic factor is $\frac12\sum_ew_\pm(\lvert1-e\rvert)2^{-e}\in[0.796047,0.796048]$; the odd product is in $[1.176329,1.176330]$.

## 8. Cubic characters in base 2 (A2.4)

Let $\chi$ be a cubic Dirichlet character modulo $M$, $c=1*\chi=x+y\omega$, $c_+=2x-y$, $c_-=y$, and $L_\pm(2^k)=\sum c_\pm(n)2^{-kn}$, as in [GF-31](../../docs/results.md#gf-31), `notes/phase23/dense-characters-and-nonfundamental-forms.md` §1. On its support $c(n)=A(n)e^{i\pi t(n)/3}$ with $A(n)=\prod_{\chi(p)=1}(e_p+1)$, so $c_\pm(n)/A(n)\in\{0,\pm1,\pm2\}$.

**Proposition 8.1 (Paper proof; Finite certificate).** $w_\pm(c_\pm(n))\le G_\chi(n)$, where $G_\chi$ is multiplicative with $G_\chi(p^e)=w_\pm(e+1)$ if $\chi(p)=1$, $G_\chi(p^e)=\mathbf 1[e\not\equiv2\ (3)]$ if $\chi(p)\in\{\omega,\bar\omega\}$, and $G_\chi(p^e)=1$ if $p\mid M$. Its mean is

```math
W_\chi=\prod_{\chi(p)=1}\Bigl(1-\frac1p\Bigr)\sum_e\frac{w_\pm(e+1)}{p^e}\prod_{\chi(p)\in\{\omega,\bar\omega\}}\frac{1-p^{-2}}{1-p^{-3}},
```

certified as $W_\chi\in[0.756903,0.756905]$, $[0.804514,0.804516]$ and $[0.789313,0.789314]$ for $M=7,9,13$. So by Theorem 7.1, **$L_\pm(2^k)$ is not 2-normal in base 2 for every $k\ge4$**, with $D^-(L_\pm(16);2)\ge0.1215,\ 0.0977,\ 0.1053$ respectively. This complements GF-31, which proves simple nonnormality in radix $2^k$. Modulo 7 the majorant just misses $k=3$ ($W_\chi>3/4$). With the weighted phase law of GF-31, an External input (Selberg–Delange), $c_-$ gains the factor $2/3$ and reaches $k=3$.

*Proof.* $w_\pm(2A)=w_\pm(A)\le\prod_{\chi(p)=1}w_\pm(e_p+1)$, and $c(n)\ne0$ exactly when $e_p\not\equiv2\pmod3$ at every $p$ with $\chi(p)\in\{\omega,\bar\omega\}$. Since $G_\chi(p)=1$ for all $p$, Lemma 3.1 applies. ∎

*Remark (quartic characters; limitation of the method).* For a quartic $\chi$, the local values are $c(p^e)=e+1$ when $\chi(p)=1$, they lie in $\{1,0\}$ when $\chi(p)=-1$, and they lie in $\{1,1\pm i,\pm i,0\}$ when $\chi(p)=\pm i$. Since $(1+i)^2=2i$, on its support $c(n)$ is a unit times $A(n)\,2^a(1+i)^{\epsilon}$ with $\epsilon\in\{0,1\}$. Every additive projection $\Phi:\mathbb Z[i]\to\mathbb Z$ therefore satisfies $w_\pm(\Phi(c(n)))\le K_\Phi\,w_\pm(A(n))$. Here $K_\Phi$ is the largest signed weight among the finitely many values $\Phi(u)$ and $\Phi(u(1+i))$, where $u$ ranges over the units. The proof of Proposition 8.1 does not transfer verbatim. At the primes with $\chi(p)=-1$, a set of relative density $\frac14$ with $\sum1/p=\infty$, we have $c(p)=1+\chi(p)=0$, so the support majorant has $G(p)=0$ infinitely often: Lemma 3.1 does not apply to it, and its Euler product is $0$. Truncation turns this into a stronger conclusion. Fix $P$ and let $G_P$ be multiplicative with $G_P(p^e)=w_\pm(e+1)$ if $\chi(p)=1$, $G_P(p^e)=\mathbf 1[e\not\equiv3\ (4)]$ if $\chi(p)=\pm i$, $G_P(p^e)=\mathbf 1[2\mid e]$ if $\chi(p)=-1$ and $p\le P$, and $G_P(p^e)=1$ otherwise. Since $c(n)=0$ unless $e_p$ is even at every $p$ with $\chi(p)=-1$ and $e_p\not\equiv3\pmod4$ at every $p$ with $\chi(p)=\pm i$, we get $w_\pm(\Phi(c(n)))\le K_\Phi G_P(n)$. Now $G_P(p)=1$ for every $p>P$ and $G_P$ grows polynomially, so Lemma 3.1 applies and gives $\limsup_X\frac1X\sum_{n\le X}w_\pm(\Phi(c(n)))\le K_\Phi W_0\prod_{p\le P,\ \chi(p)=-1}\frac p{p+1}$. Here $W_0<\infty$ is the product of the local factors at the primes with $\chi(p)\ne-1$, and $\frac p{p+1}=(1-\frac1p)\sum_{e\ \rm even}p^{-e}$. Letting $P\to\infty$ shows that the mean is $0$. The bound $\lvert\Phi(c(n))\rvert\ll\tau(n)$ gives **(H)**, so Theorem 7.1 yields $(f_{01}+f_{10})(N)\to0$, and Proposition 2.4(4) for every $m\ge2$ gives $D^-(L_\Phi(2^k);2)=1$ for **every** $k\ge1$ (*Paper proof sketch; no Tauberian input and no constants needed*). For odd order $h\ge5$, $1+\zeta_h^j$ is in general not a power of 2 times a root of unity, and $\Phi(c(n))$ is an integer linear form in the coordinates, in an integral basis of $\mathbb Z[\zeta_h]$, of a product of such factors. Bounding the signed weights of these coordinates by subadditivity gives a multiplicative majorant whose value is at least $2$ at the primes with $\chi(p)\ne0,1$, so it grows like $2^{\#\{p\parallel n:\ \chi(p)\ne0,1\}}$ over a positive proportion of primes. Its mean diverges, and the method as set up gives nothing. This does not show that the true mean of $w_\pm(\Phi(c(n)))$ is infinite. For any multiplicative integer sequence the same reasoning applies. The majorant has finite mean whenever, at all primes outside a set with $\sum1/p<\infty$, the value $a(p)$ is $0$ or a signed power of 2 (with polynomially bounded $a(p^e)$); bound $G$ by the majorant with $G(p)=1$ at the zeros and apply Lemma 3.1. If instead $w_\pm(a(p))\ge2$ on a set of primes of positive relative density and $a(p)\ne0$ for almost all $p$, the majorant mean diverges like a positive power of $\log X$ (Wirsing, External input). The periodic-weight divisor sums of GF-31 §1 fall under this criterion: the factors $2^{\#\{p\parallel n:\,p\equiv1\ (M)\}}$ dividing $a(n)$ cost nothing in $w_\pm$, and what matters is the odd part at the primes.

## 9. The $E(4)$ boundary (A4.1)

**Theorem 9.1 (Paper proof).** For $E(2^k)$ in base 2, Theorem 2.2 is exact:

```math
f_1(N;E(2^k),2)=\frac1N\sum_{n\le N/k}s_2(\tau(n))-\frac{\kappa_k(N)}N+O\Bigl(\frac{\log N}N\Bigr)=\frac{C_{\rm true}}k-\frac{\kappa_k(N)}N+o(1),
```

where $\kappa_k(N)$ is the total column carry (Lemma 1.1). Consequently:

1. $E(4)$ is simply normal in base 2 **if and only if** $\kappa_2(N)/N\to(C_{\rm true}-1)/2\in[0.169551,\,0.169558]$. It satisfies $\limsup f_1<\frac12$ if and only if $\liminf\kappa_2(N)/N>(C_{\rm true}-1)/2$.
2. *Obstruction.* Every $\tau(n)\ge1$ has $s_2(\tau(n))\ge1$, with equality failing on a set of positive density (for example $p^2\parallel n$, where $s_2(3)=2$). So $C_{\rm true}>1$, and the zero-carry bound gives only $\limsup f_1\le C_{\rm true}/2\le0.66956$. No argument that bounds carries below by zero, and more generally no coefficient-mass functional $\mu\ge1$ on nonzero integers, can decide $E(4)$. A proof of $\limsup f_1<\frac12$ must exhibit $\liminf\kappa_2(N)/N>(C_{\rm true}-1)/2$, where $(C_{\rm true}-1)/2\ge0.169551$. Simple nonnormality could also arise in other ways, for example if $\kappa_2(N)/N$ does not converge.
3. For $E(2)$ the analogous condition is $\kappa_1(N)/N\to C_{\rm true}-\frac12\in[0.839103,0.839116]$. For $k\ge3$ simple normality would require $\kappa_k/N\to C_{\rm true}/k-\frac12<0$, which is impossible; this is consistent with Theorem 4.1.

*Measurement (finite, §11).* At $N=2^{17}$, $\kappa_2(N)/N=0.17420$ for $E(4)$ and $f_1=0.49490$. The carry density currently exceeds the threshold, but no asymptotic conclusion follows.

## 10. The $E^*(4)$ boundary (A4.2)

$E^*(4)=\sum_n2^{-q(n)}$ with $q(n)=2n-\omega(n)$, so every term is a single bit.

**Theorem 10.1 (Paper proof).** We have $f_1(N;E^*(4),2)=\frac12-\kappa^*(N)/N+O(\log N/N)$. Hence:

1. $\limsup_Nf_1(N;E^*(4),2)\le\frac12$, so the digit 1 never has limiting frequency above $1/2$.
2. $E^*(4)$ is simply normal in base 2 **if and only if** $\kappa^*(N)=o(N)$.
3. $\kappa^*(N)\ge\frac12\#\{n\le N/2:\exists\,n'>n,\ q(n')=q(n)\}-O(\log N)$. Indeed a column with $r\ge2$ operands sends $\lfloor r/2\rfloor\ge(r-1)/2$ carries, and partners satisfy $n'-n\le\frac12\log_2n'$.

The **collision set** $\mathcal C=\{n:\exists\,n'>n,\ \omega(n')-\omega(n)=2(n'-n)\}$ therefore controls the boundary.

**Proposition 10.2 (Conditional).** If $\mathcal C$ has positive upper density $\delta^+$, then $\liminf f_1(N;E^*(4),2)\le\frac12-\delta^+/4$, and $E^*(4)$ is simply nonnormal in base 2. If $\mathcal C$ has positive lower density $\delta^-$, then $\limsup f_1\le\frac12-\delta^-/4$ and $D^-(E^*(4);2)\ge\delta^-/4$.

*Status.* For each fixed gap $d$, a bivariate Erdős–Kac theorem for $(\omega(n),\omega(n+d))$ shows (External input; it follows from the method of moments with a sieve) that $\{n:\omega(n+d)-\omega(n)=2d\}$ has density zero. Positive density of $\mathcal C$ needs a union over $d\ll\sqrt{\log\log n}$ with uniform local lower bounds of size $1/\sqrt{\log\log n}$, beyond Erdős–Pomerance–Sárközy-type results. This is **Open**.

*Heuristic (not evidence).* If $\omega$ at nearby integers behaves like independent normals with variance $L=\log\log n$, the expected number of later partners is $\sum_{d\ge1}(4\pi L)^{-1/2}e^{-d^2/L}\to\frac14$. The positions $q(n)$ then become locally Poisson with intensity $\frac12$ as $L\to\infty$. Running the stationary Poisson column-carry chain predicts $f_1(E^*(4))\to0.36353$ (and $0.27337$ for $E^*(8)$), approached at speed $\log\log N$. The measured $f_1(E^*(4))=0.43910$ at $N=2^{17}$ and the collision-position density $0.0604$ are consistent with a slow approach. They are finite measurements only.

The base-3 threshold $E^*_3(3)$ is analogous. Its digit average is $1-2\kappa/N+o(1)$, and, in the absence of incoming carries, a carry needs a three-fold collision $n_1-\omega(n_1)=n_2-\omega(n_2)=n_3-\omega(n_3)$ with $n_1<n_2<n_3$.

## 11. Finite measurements only

These prefixes are computed exactly. The tail is bounded with 64 guard digits using $\lvert a(n)\rvert\le\tau(n)\le2\sqrt n$, or $\le4n$ for $\tau_3$ and $3^{\omega}$, and the script asserts that the floor is determined. The statistics are **finite measurements only**: they prove nothing about limits.

| Constant (base 2), $N=2^{17}$ | $f_1$ | $f_{01}+f_{10}$ | coefficient mass $/N$ | carry $\kappa/N$ | proved asymptotic bound |
| --- | --- | --- | --- | --- | --- |
| $E(2)$ | 0.50923 | 0.48866 | 1.33854 | 0.82931 | none |
| $E(4)$ | 0.49490 | 0.54652 | 0.66910 | 0.17420 | $f_1\le0.6696$ |
| $E(8)$ | 0.40815 | 0.54326 | 0.44604 | 0.03790 | $f_1\le0.4464$ |
| $E(16)$ | 0.32872 | 0.48445 | 0.33459 | 0.00587 | $f_1\le0.3348$ |
| $E_{\rm odd}(4)$ | 0.48634 | 0.58103 | 0.58001 | 0.09368 | $f_1\le0.5804$ |
| $E_{\rm odd}(8)$ | 0.37682 | 0.57971 | 0.38657 | 0.00976 | $f_1\le0.38689$ |
| $E^*(4)$ | 0.43910 | 0.60380 | 0.50000 | 0.06091 | $f_1\le1/2$ |
| $E^*(8)$ | 0.32079 | 0.56040 | 0.33333 | 0.01254 | $f_1\le1/3$ |
| $E_+(2)$ | 0.49297 | 0.49982 | 0.90792 ($w_\pm$) | — | none |
| $E_+(4)$ | 0.40479 | 0.42993 | 0.45390 | — | none |
| $E_+(8)$ | 0.33718 | 0.36037 | 0.30252 | — | none |
| $E_+(16)$ | 0.30349 | 0.30164 | 0.22694 | — | $f_{01}+f_{10}\le0.4541$ |

| Constant (base $b$) | $N$ | digit frequencies $0,1,\dots$ | average (uniform) | proved |
| --- | --- | --- | --- | --- |
| $E(9)$, base 3 | 40000 | 0.2764 0.3565 0.3671 | 1.0907 (1) | nothing (barrier) |
| $E(3)$, base 3 | 40000 | 0.3209 0.3291 0.3500 | 1.0291 (1) | nothing |
| $\sum\tau_3(n)9^{-n}$, base 3 | 40000 | 0.4936 0.3364 0.1700 | 0.6764 (1) | average $\le0.7538$ |
| $\sum3^{\omega(n)}9^{-n}$, base 3 | 40000 | 0.5576 0.3848 0.0576 | 0.5000 (1) | average $\le1/2$ |
| $E(100)$, base 10 | 20000 | 0.3586 0.1107 0.1531 0.0141 0.1598 0.0016 0.0826 0.0004 0.1174 0.0016 | 2.5589 (4.5) | nothing (barrier) |
| $E(16)$, base 4 | 40000 | 0.4340 0.2453 0.2275 0.0931 | 0.9798 (1.5) | not simply normal |

At $X=6\cdot10^5$, $\frac1X\sum_{n\le X}s_2(\tau(n))=1.338943$ and $\frac1X\sum w_\pm(a_+(n))=0.908092$, consistent with the certified limits. The $E(100)$ row shows why finite data must not be used as proof. The prefix looks far from uniform, yet Theorem 5.1 shows that the coefficient mass grows without bound, so the method cannot decide this constant.

## 12. Open problems

1. $E(4)$, $E(2)$, $E_{\rm odd}(4)$: decide the carry density (Theorem 9.1).
2. $E^*(4)$: prove that $\mathcal C$ has positive upper density (Proposition 10.2).
3. $E_+(2^k)$ for $k\le3$: below the method floor.
4. $E(b^k)$ for $b$ not a power of 2, including $E(9)_3$ and $E(100)_{10}$: needs a non-mass method (Theorem 5.1).
5. $D^+<1$ and $K_2$-membership for $E(2^k)$, $k\ge3$. The results here bound $D^-$ from below only. By the kernel-verified `discrepancy_lt_one_iff_transitions`, $D^+(x;2)<1$ is equivalent to a positive lower transition density $\liminf(f_{01}+f_{10})>0$. That requires a *lower* bound on the 1-bits that survive carries and do not merge into long runs, which digit mass does not supply. A lower bound $\liminf f_1>0$ alone does not suffice, because the orbit could still concentrate at $0$ from both sides.

## 13. Historical Lean blueprint (superseded by compiled `NormalityChecker/DigitMassTransfer.lean`)

The snippet below is the historical pre-formalization blueprint written before Stage 3 compilation. It has been **superseded** by the compiled, kernel-verified unconditional declarations in [`NormalityChecker/DigitMassTransfer.lean`](../../NormalityChecker/DigitMassTransfer.lean) (specifically `tsum_tauDigitKernel_div_le` at lines 1663–1751 proving $\le 29/20$, `erdosBorwein_two_pow_digitFreq_limsup_le` at lines 2143–2157 proving $\limsup f_1 \le 29/(20k)$ **unconditionally without any `hmean` premise**, and `erdosBorwein_two_pow_not_simplyNormal` / `erdosBorwein_two_pow_not_simplyNormal_pow` at lines 2277–2337; the sharper $C_{\rm true}/k \le 1.339116/k$ bound in Theorem 4.1 remains a Paper proof + Finite certificate). Names below follow `Basic.lean` (`shift`, `frequency`), `BinaryDiscrepancy.lean` (`radixDiscrepancy`, `transitionFrequency`) and `Phase22Cores.lean` (`erdosBorweinPlusCoeff`). The first group (L1–L9) is finite combinatorics. L10–L12 connect to the existing discrepancy API. L13–L15 carry the analytic content.

```lean
namespace NormalityChecker.DigitMassTransfer
open Finset

/-- Base-`b` digit sum `s_b(n)`. -/
def digitSum (b n : ℕ) : ℕ := (Nat.digits b n).sum
/-- Number of nonzero base-`b` digits `w_b(n)`. -/
def nonzeroDigits (b n : ℕ) : ℕ := ((Nat.digits b n).filter (· != 0)).length  -- `List.filter` takes `α → Bool`

/-- Minimal signed binary weight (NAF weight), by the defining recursion. -/
def signedWeight : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then signedWeight ((n + 2) / 2)
    else 1 + min (signedWeight ((n + 1) / 2)) (signedWeight ((n + 3) / 2))
decreasing_by all_goals omega

/-- Adjacent unequal bits of the two's-complement expansion of `A`. -/
def transitions (A : ℤ) : ℕ :=
  let B : ℕ := if 0 ≤ A then A.toNat else (-A - 1).toNat
  digitSum 2 (B ^^^ (B / 2))

-- L1 Kummer (two summands) with an explicit carry count
/-- Carries produced when adding `a` and `c` in base `b` with incoming carry `cin`
(once `a = c = 0` no further carry can occur, since `0 + 0 + 1 < b`). -/
def carries (b cin a c : ℕ) : ℕ :=
  if b ≤ 1 ∨ (a = 0 ∧ c = 0) then 0 else
    let o := if b ≤ a % b + c % b + cin then 1 else 0
    o + carries b o (a / b) (c / b)
termination_by a + c   -- a / b + c / b < a + c since b ≥ 2 and a + c > 0
theorem digitSum_add_add_carries (b a c : ℕ) (hb : 2 ≤ b) :
    digitSum b (a + c) + (b - 1) * carries b 0 a c = digitSum b a + digitSum b c

-- L2 subadditivity / submultiplicativity
theorem digitSum_add_le (b a c : ℕ) (hb : 2 ≤ b) :
    digitSum b (a + c) ≤ digitSum b a + digitSum b c
theorem digitSum_mul_le (b a c : ℕ) (hb : 2 ≤ b) :
    digitSum b (a * c) ≤ digitSum b a * digitSum b c
theorem digitSum_mul_pow (b a t : ℕ) (hb : 2 ≤ b) : digitSum b (a * b ^ t) = digitSum b a
theorem nonzeroDigits_add_le (b a c : ℕ) (hb : 2 ≤ b) :
    nonzeroDigits b (a + c) ≤ nonzeroDigits b a + nonzeroDigits b c
theorem nonzeroDigits_mul_le (b a c : ℕ) (hb : 2 ≤ b) :
    nonzeroDigits b (a * c) ≤ min (digitSum b a * nonzeroDigits b c)
      (2 * nonzeroDigits b a * nonzeroDigits b c)
-- L3 failure of naive submultiplicativity for b ≥ 3
theorem nonzeroDigits_pred_sq (b : ℕ) (hb : 3 ≤ b) :
    nonzeroDigits b ((b - 1) * (b - 1)) = 2 ∧ nonzeroDigits b (b - 1) = 1

-- L4 binary successor law, i.e. h(p^e) = 1 - v₂(e+1)
theorem digitSum_two_succ (m : ℕ) :
    digitSum 2 (m + 1) + padicValNat 2 (m + 1) = digitSum 2 m + 1

-- L5 signed weight
theorem signedWeight_le_digitSum (n : ℕ) : signedWeight n ≤ digitSum 2 n
theorem signedWeight_two_mul (n : ℕ) : signedWeight (2 * n) = signedWeight n
theorem signedWeight_add_le (m n : ℕ) : signedWeight (m + n) ≤ signedWeight m + signedWeight n
theorem signedWeight_sub_le (m n : ℕ) (h : n ≤ m) :
    signedWeight (m - n) ≤ signedWeight m + signedWeight n
theorem signedWeight_mul_le (m n : ℕ) : signedWeight (m * n) ≤ signedWeight m * signedWeight n

-- L6 transition increments
theorem transitions_add_two_pow (A : ℤ) (m : ℕ) :
    (transitions (A + 2 ^ m) : ℤ) ≤ transitions A + 2 ∧
    (transitions A : ℤ) ≤ transitions (A + 2 ^ m) + 2
theorem transitions_add_le (A c : ℤ) :
    transitions (A + c) ≤ transitions A + 2 * signedWeight c.natAbs

-- L7 exact prefix decomposition (Theorem 2.1); `x = ∑ a(n+1) b^{-k(n+1)}`
theorem floor_pow_mul_eq_head_add_floor_tail {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (a : ℕ → ℤ) (hs : Summable fun n : ℕ => |(a (n + 1) : ℝ)| / (b : ℝ) ^ (k * (n + 1)))
    (N : ℕ) :
    ⌊(b : ℝ) ^ N * ∑' n : ℕ, (a (n + 1) : ℝ) / (b : ℝ) ^ (k * (n + 1))⌋ =
      (∑ n ∈ Icc 1 (N / k), a n * (b : ℤ) ^ (N - k * n)) +
      ⌊∑' m : ℕ, (a (N / k + 1 + m) : ℝ) * (b : ℝ) ^ N / (b : ℝ) ^ (k * (N / k + 1 + m))⌋

-- L8 unsigned prefix digit-sum bound (Theorem 2.2), stated for the integer prefix
theorem digitSum_prefix_le {b k : ℕ} (hb : 2 ≤ b) (a : ℕ → ℕ) (N t : ℕ) :
    digitSum b ((∑ n ∈ Icc 1 (N / k), a n * b ^ (N - k * n)) + t) ≤
      (∑ n ∈ Icc 1 (N / k), digitSum b (a n)) + digitSum b t

-- L9 signed prefix transition bound (Theorem 7.1)
theorem transitions_prefix_le {k : ℕ} (a : ℕ → ℤ) (N : ℕ) (t : ℤ) :
    transitions ((∑ n ∈ Icc 1 (N / k), a n * 2 ^ (N - k * n)) + t) ≤
      2 * (∑ n ∈ Icc 1 (N / k), signedWeight (a n).natAbs) + 2 * signedWeight t.natAbs

-- L10 frequency criteria (Proposition 2.4(2),(4))
theorem radixDiscrepancy_ge_nonzero_freq (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (N : ℕ) (hN : 0 < N) :
    ((b - 1 : ℝ) / b) - frequency (shift b x) (1 / b) 1 N ≤ radixDiscrepancy b x N
theorem binaryDiscrepancy_ge_half_sub_transition (x : ℝ) (N : ℕ) (hN : 0 < N) :
    1 / 2 - transitionFrequency x N ≤ radixDiscrepancy 2 x N

-- L11 radix descent (Proposition 2.4(5))
theorem radixDiscrepancy_descent (b k N : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) (x : ℝ) :
    radixDiscrepancy b x (k * N) ≤
      ((b : ℝ) ^ k - 1) / (k * ((b : ℝ) - 1)) * radixDiscrepancy (b ^ k) x N

-- L12 zero-run bound (Proposition 2.4(3)), base 2
theorem radixDiscrepancy_ge_zero_run (x : ℝ) (m N : ℕ) (hN : 0 < N) :
    1 - (m : ℝ) * ((N + m : ℝ) / N) * frequency (shift 2 x) (1 / 2) 1 (N + m) - 2⁻¹ ^ m ≤
      radixDiscrepancy 2 x N

-- L13 squarefull convolution mean value (Lemma 3.1). Multiplicativity of `G` is not needed
-- for the limit; it is used only to rewrite the limit as an Euler product.
/-- Möbius as a real arithmetic function, through the `ℤ → ℝ` coercion of arithmetic functions
(`ArithmeticFunction.intCoe`); pointwise it is `n ↦ ((ArithmeticFunction.moebius n : ℤ) : ℝ)`. -/
noncomputable abbrev moebiusReal : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
theorem tendsto_average_of_summable_conv_mobius (G : ArithmeticFunction ℝ)
    (hs : Summable fun n : ℕ => |(G * moebiusReal) n| / n) :
    Filter.Tendsto (fun X : ℕ => (∑ n ∈ Icc 1 X, G n) / (X : ℝ)) Filter.atTop
      (nhds (∑' n : ℕ, (G * moebiusReal) n / n))

-- L14 local identity (Corollary 3.3(3))
theorem local_factor_digitSum_two (p : ℕ) (hp : 2 ≤ p) :
    (1 - (p : ℝ)⁻¹) * ∑' e : ℕ, (digitSum 2 (e + 1) : ℝ) / (p : ℝ) ^ e =
      ∑' j : ℕ, (p : ℝ) / ((p : ℝ) ^ (2 ^ j) + 1)

-- L15 headline (SUPERSEDED blueprint signature; compiled unconditional declaration in
-- `NormalityChecker/DigitMassTransfer.lean` lines 2143-2157 drops `hmean` and proves `≤ 29 / (20 * k)`)
theorem erdosBorwein_two_pow_digitFreq_limsup_le (k : ℕ) (hk : 1 ≤ k)
    (hmean : ∀ᶠ X in Filter.atTop,
      (∑ n ∈ Icc 1 X, (digitSum 2 (Nat.divisors n).card : ℝ)) / X ≤ 1.4036) :
    Filter.limsup (fun N => frequency (shift 2 (∑' n : ℕ, (1 : ℝ) / (2 ^ (k * (n + 1)) - 1)))
      (1 / 2) 1 N) Filter.atTop ≤ 1.4036 / k
-- L15' corollary: for 3 ≤ k, the digit 1 does not have frequency 1/2, so E(2^k) is not
-- simply normal in base 2 (1.4036 / 3 < 1/2), hence not simply normal in base 2^j for every j.
```

L15 needs only the majorant bound $C<1.4036$, or even $C<3/2$, which closes $k=3$. An elementary closed-form route to $C<3/2$ avoids the long product. Write $L(p)=\sum_{j\ge0}p/(p^{2^j}+1)$ for the local factor of $C$. Since $L(p)\le1+p^{-2}$ for $p\ge3$, $C\le\frac45L(2)\prod_p(1+p^{-2})=\frac45L(2)\cdot\frac{15}{\pi^2}\le\frac45\cdot1.19213\cdot1.51982<1.4495<\frac32$, with $L(2)=1.192126\ldots$ and $15/\pi^2=1.519817\ldots$, using $\zeta(2)=\pi^2/6$ and $\zeta(4)=\pi^4/90$, which are in Mathlib. The bound $L(p)\le1+p^{-2}$ follows from $L(p)-1=\frac{p-1}{(p+1)(p^2+1)}+\sum_{j\ge2}\frac p{p^{2^j}+1}$. A formalizer should prove L1–L12 first; L13 and L14 are the analytic core.

## 14. Proposed registry entry (text only; the registry is not edited here)

> **Phase 24 Track A — dense digit-mass transfer.** (1) Exact truncation/carry-tail transfer for $\sum a(n)b^{-kn}$, $a\ge0$, with carry tail $O(\log N)$ (the "+1" form fails). Elementary mean values via the squarefull convolution and the independent-exponent model. $E(2^k)$ is simply nonnormal in every base $2^j$ for every $k\ge3$, with $\limsup f_1\le C_{\rm true}/k$, $C_{\rm true}\in[1.339103,1.339116]$, explicit $D^-$ in bases 2 and $2^k$, and $D^-(E(2^k);2)\to1$. (2) Barrier: for $b$ not a power of 2 the mean digit mass of $\tau(n)$ is infinite (Senge–Straus). Digit mass of $\tau_r$ in base $b$ is bounded if and only if $r$ and $b$ are multiplicatively dependent. Certified thresholds hold for $E_{\rm odd}$, $\tau_4$, $\tau_8$, $\tau_{16}$, unitary and base-$b$ $\tau_b$ families. (3) Signed transition transfer: $E_+(2^k)$ ($k\ge4$, optimal for the method) and cubic $L_\pm(2^k)$ ($k\ge4$) are not 2-normal in base 2, with explicit $D^-$. (4) Exact carry characterizations of the $E(4)$ and $E^*(4)$ thresholds. Evidence: Paper proofs; Finite certificates in `scripts/phase24_digit_mass.py`; External input Senge–Straus (1973) for the barrier and the dichotomy; Conditional for Proposition 10.2.
