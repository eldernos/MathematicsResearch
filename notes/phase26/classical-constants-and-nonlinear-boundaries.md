# Classical constants, partition constants, nonlinear equality boundaries and algebraic irrationals: $q$-Padé forms for Euler's product, logarithmic transitions for $1/E_b$, exact reset thresholds for $\ln 2$, and the cubic depth–gap obstruction

Phase 26, Track F (`F1`–`F4`). This note continues Phase 26 Track B ([`arithmetic-hankel-determinants.md`](arithmetic-hankel-determinants.md), cited as *B*), Phase 25 `GF-47` ([`classical-constants-frontier.md`](../phase25/classical-constants-frontier.md)), `GF-45` ([`partitions-and-reciprocals.md`](../phase25/partitions-and-reciprocals.md)) and `GF-46` ([`nonlinear-and-badly-approx.md`](../phase25/nonlinear-and-badly-approx.md)). Companion exact verifier: [`scripts/phase26_classical_nonlinear.py`](../../scripts/phase26_classical_nonlinear.py).

---

## 0. Definitions, evidence labels and scope

**Radix notation.** For an integer base $b\ge2$ and real $x$, $d_j(x)$ is the $j$-th base-$b$ digit of $\{x\}$ (expansions not ending in $(b-1)^\infty$). A *constant run of length $L$ after position $N$* means $d_{N+1}=\dots=d_{N+L}$. A *transition* is an index $j$ with $d_j\ne d_{j+1}$, and $\chi_N(x)$ is the number of transitions with $j<N$. $F_b=(b-1)^{-1}\mathbb Z/\mathbb Z$ is the set of fixed points of $t\mapsto bt \bmod 1$; an *escape* at time $j$ is $\|(b-1)b^jx\|\ge 1/(2b)$, where $\|u\|$ is the distance from $u$ to $\mathbb Z$. $D_N(x;b)$ is the extreme discrepancy of $(\{b^nx\})_{0\le n<N}$. The irrationality exponent is $\mu(x)=\sup\{\mu:\ |x-p/q|<q^{-\mu}\text{ for infinitely many }p/q\}$.

**Euler's product and the partition constant.** $E_b=\prod_{j\ge1}(1-b^{-j})$ and $P_b=1/E_b=\sum_{n\ge0}p(n)b^{-n}$. With $q=1/b$, $(z;q)_k=\prod_{i<k}(1-zq^i)$, and

```math
D_k=\prod_{j=1}^{k}(b^j-1),\qquad D_0=1,\qquad \left[{n\atop r}\right]_b=\frac{D_n}{D_rD_{n-r}}\in\mathbb Z ,
```

so $(q;q)_k=D_k\,b^{-k(k+1)/2}$.

**BBP states of $\ln2$.** $s_n=\sum_{k\le n}2^{n-k}/k=A_n/Q_n$ (lowest terms), $x_n=\{s_n\}$, $T_n=2^n\ln2-s_n\in(\frac1{n+2},\frac1{n+1})$, $L_n=\operatorname{lcm}(1,\dots,n)$. As in `GF-47`, a *reset countermodel* is a sequence $\tilde x_n\in\mathbb Q/\mathbb Z$ ($n\ge n_0$) satisfying $\tilde x_{n+1}=2\tilde x_n+\frac1{n+1}$ except at reset times $n_1<n_2<\cdots$. It is *uniform* if $\limsup_n\|\tilde x_n\|<\frac14$ (`GF-47` Theorem 3.6 has $\|\tilde x_n\|\to0$).

**Equality-boundary cube.** As in `GF-46`, with $B=b^{\operatorname{ord}_pb}$, $C_s(d)=\sum_{i\ge1}p^{-sv_p(i)}B^{-i^d}$, $X=C_s(d)^d=\sum_mc_mB^{-m}$, prefixes $R_M=\sum_{m\le M}c_mB^{M-m}$, depth $e_M=\max(0,-v_p(R_M))$ (so $\operatorname{den}\{R_M\}=p^{e_M}$) and tails $T_M=B^MX-R_M>0$. The *flagship cube* is $(b,p,s,d,B)=(2,3,1,3,4)$, $C_1(3)=\sum_{i\ge1}3^{-v_3(i)}4^{-i^3}$.

**Evidence labels** ([`docs/research-objectives.md`](../../docs/research-objectives.md)): *Paper proof* (complete proof here); *Finite certificate* (exact `int`/`Fraction` computation, or outward-rounded rational enclosure, in the companion script); *External input* (published theorem used without re-proof, listed in §6); *Conditional*; *Finite measurement* (`[finite]`, bears on no limit); *Open*. No cross-model review was used to produce this note. Any later cross-model review is not independent human peer review.

**Scope statement.** **Nothing in this note proves normality, simple normality, simple nonnormality, $D^+<1$, $D^->0$, or (non)membership in $K_b$ for any constant of the fixed roster `BC-01`…`BC-50`, nor for $E_b$, $P_b$, $X_{b,m}$ or $C_1(3)^3$. No benchmark status changes.** Every new theorem below is a Diophantine, arithmetic or structural statement (Objectives 3 and 4). Where a digit consequence is drawn, it is a run, transition, escape or finite-$N$ discrepancy-gap statement, and the transfer from approximation to digits is proved explicitly (Lemma 2.0).

---

## Summary of conclusions

| Item | Result | Evidence |
| --- | --- | --- |
| **F2.1** | **$q$-Padé linear forms for Euler's product** (Thm 2.1): explicit integers $Q_n,P_n$ with $Q_nE_b-P_n=\lambda_n$, $\lvert Q_n\rvert\le3b^{2n^2+n}$ ($n\ge1$), $\lvert Q_n\rvert\ge\tfrac12b^{2n^2+n}$ ($n\ge2$), $\tfrac{13}{15}E_b\,b^{-(3n+2)(n+1)/2}\le\lvert\lambda_n\rvert\le2b^{-(3n+2)(n+1)/2}$, consecutive pairs independent (all $n\ge1$, all $b\ge2$) | Paper proof (+ Euler's $q$-exponential identity, External input); finite certificate |
| **F2.2** | **$\mu(E_b)=\mu(P_b)\le 7/3$ for every base $b\ge2$**, with $\lvert AE_b-B\rvert\ge\frac16b^{-2(n_A+1)^2-(n_A+1)}$ and, when $n_A\ge3$, the explicit form $\lvert AE_b-B\rvert\ge\frac16(4A)^{-4/3}b^{-17n_A/3-3}$, $n_A<\frac16(1+\sqrt{1+24\log_b4A})$ (Thm 2.2). The exponent $7/3$ is Bundschuh's (1970); Thm 2.2 is a self-contained explicit reproof (§2.2, §7) | Paper proof; finite certificate |
| **F2.3** | **Runs of $P_b$ are linear**: every constant run after $N$ has length $\le\frac43N+4.63\sqrt N+O_b(1)$, against `GF-45` E4's $\frac38N^2$; hence $\chi_N(P_b)\ge(\frac1{\ln(7/3)}-o(1))\ln N$, as many escapes, and $1-D_N(P_b;b)\gg_b(\log N)/N$. **This improves `GF-45` E4's $\log\log N$ to $\log N$** (Cor. 2.3) | Paper proof |
| **F2.4** | **The $N^2$ isolation scale is sharp for $b$-power denominators** (Prop. 2.4): $\|b^gE_b\|\ge\frac12b^{-\sqrt{8g/3}-2}$ for all $g$, so every certificate built on approximants with denominators $b^g$ gives at best runs $\le(\frac38+o(1))N^2$; positive Padé quality $\sigma=\frac34$ with cyclotomic denominators $D_n$ is what breaks it | Paper proof; finite certificate |
| **F2.5** | **Run-method ceiling** (Prop. 2.5): uniform run bounds $L(n)\le(\lambda-1)(n+1)+1$ are compatible with exactly $\log_\lambda N+O(1)$ transitions; going beyond $\log N$ for $X_{b,m}$ or $P_b$ is equivalent to sublinear runs (a $b$-adic Ridout property, Prop. 2.6), which is open | Paper proof; finite certificate |
| **F1.1** | **Band-indexed exclusion law and CRT decoupling** (Lemma 1.1): for $M$ a squarefree product of **odd** primes $p\le n$ with $p^2>n_{\rm end}-1$, a translate $a/M$ keeps the exact denominators on a window iff each local residue avoids $\{-2^{n-m}s_m\bmod p\}$ over the window's bands $m$ (or is $0$ at a drop band); at most $\lceil(n_{\rm end}-n-1)/p\rceil+1$ bands per prime. Same-band and cross-band large-prime data are a CRT product, with zero cross-prime coupling | Paper proof; finite certificate |
| **F1.2** | **Full-denominator geometric resets exist for every ratio $\rho<1+1/\ln2=2.442695\ldots$** (Thm 1.2), beyond `GF-47`'s $\frac32$ and top-band $1.72134\ldots$; an explicit exact block $[1000,2000)$ of ratio $2$ is certified | Paper proof (+ PNT, External input); finite certificate |
| **F1.3** | **Translate-robust dyadic measure** (Thm 1.3): $\lvert2^M\ln2-x\rvert\ge2^{-(5.178813+o(1))M}$ for every rational $x$ whose denominator divides $L_M$, from Track B's prime-centered forms, which are blind to $p$-integral shifts. The general-denominator measure (Marcovecchio) gives only $2^{-(7.7316+o(1))M}$ here | Paper proof (+ PNT); finite certificate |
| **F1.4** | **$\Omega(\log N)$ resets are necessary** (Thm 1.4): every uniform reset countermodel with reset denominators dividing $L_{n_i}$ has $n_{i+1}\le(6.178813+o(1))n_i$, so at least $(0.3806-o(1))\log_2N$ resets. Together with F1.2 and `GF-47`, $\Theta(\log N)$ is the exact order, and the optimal ratio lies in $[1+1/\ln2,\,\mu_2^{\rm Hankel}]\subset[2.4426,\,6.1789]$. **This answers `GF-47` Open Question 4 for barriers in the sense of Theorem 3.6** | Paper proof (+ PNT) |
| **F3.1** | Depth recursion $C_s(z)=U(z)+p^{-s}C_s(z^{p^d})$ (Prop. 3.1) and the rational-tail inequality (Thm 3.2), which is the denominator-only ($h=0$) case of `GF-46` Thm 1.3(1) | Paper proof; finite certificate |
| **F3.2** | **Multi-packet collapse** (Thm 3.3): any finite family of exact prefixes and tail bounds is equivalent to the single packet $(R_{M^*},\tau^*)$ with the propagated tail bound. For **denominator-only ($h=0$)** certificates this packet excludes $vX\in\mathbb Z$ iff $\tau^*<1/\operatorname{lcm}(v/\gcd(v,B^{M^*}),p^{e_{M^*}})$; low-residue certificates ($h\le(1-\varepsilon)e_{M^*}$) need $\tau^*<p^{-\varepsilon e_{M^*}}$. Exact-prefix and full-residue certificates are **not** so limited (counterexamples on $C_1(3)^3$ at $M^*=91$, $v=10$ and $M^*=126$, $v=4$) | Paper proof; finite certificate |
| **F3.3** | **Finite exclusion**: $C_1(3)^3\ne u/v$ for every integer $1\le v\le6.636\times10^{24}$ (shift $M=3331$, depth $e_M=6$, empty $S_3^+$-gap $(3331,3377)$) (Thm 3.4) | Finite certificate |
| **F3.4** | **Exact exponent obstruction for denominator-only and low-residue truncation proofs** of the irrationality of $C_1(3)^3$ (Thm 3.5): an $h=0$ proof exists iff $\limsup_M(\gamma_M\log B-\log H_M-e_M\log p)=+\infty$, and a proof with $h_M\le(1-\varepsilon)e_M$ needs the same with $e_M$ replaced by $\varepsilon e_M$. Known gaps give $\gamma_M\gg(\log M)^{1/2}/(\log\log M)^2$, while depths are $\asymp\log M$ at density one. Residue-boosted proofs (`GF-46` Thm 1.3(3)) are not covered. Irrationality of $C_1(3)^3$: **Open** | Paper proof (+ Ghidelli, External input) |
| **F4** | Möbius run transfer (Thm 4.1), its sharpness (Prop. 2.5), the bounded-remainder form of $\alpha^2=D$ (Prop. 4.2) and a Track-B-consistent ledger for $\sqrt2,\sqrt3,\varphi,\pi,e,\zeta(3),\ln2,E_b,P_b$ (§4.3). Algebraic equations beat every finite-$\mu$ method only through Ridout's theorem | Paper proof; External input; finite certificate |

---

## 1. F1: $\ln 2$, global coupling across prime bands and reset windows

### 1.1 Band-indexed exclusion law; CRT decoupling of large-prime data

Fix $n$ and a window $W=[n,n_{\rm end})$. Let $M$ be a squarefree product of **odd** primes $p\le n$ with $p^2>n_{\rm end}-1$. For $p\mid M$ write $B_p(W)=\{\lfloor n'/p\rfloor:n'\in W\}$ (the *bands* met by $W$), and for an integer $a$ put $\bar a_p\equiv a\,(M/p)^{-1}\pmod p$.

**Lemma 1.1 (band-indexed exclusion law; Paper proof; Finite certificate).** With $\delta=a/M$, the translated states $x_{n'}+2^{n'-n}\delta$ have reduced denominator exactly $Q_{n'}$ for every $n'\in W$ if and only if, for every $p\mid M$:

1. if $p\mid A_m$ for some band $m\in B_p(W)$ (a `GF-47` drop event), then $\bar a_p=0$;
2. otherwise $\bar a_p\notin\operatorname{Excl}_p(W):=\{-2^{n-m}s_m\bmod p:\ m\in B_p(W)\}$.

Consequently the admissible set of $a\bmod M$ is the CRT product of the local admissible sets, and

```math
\lvert\operatorname{Excl}_p(W)\rvert\ \le\ \lvert B_p(W)\rvert\ =\ \Bigl\lfloor\frac{n_{\rm end}-1}{p}\Bigr\rfloor-\Bigl\lfloor\frac np\Bigr\rfloor+1\ \le\ \Bigl\lceil\frac{n_{\rm end}-n-1}{p}\Bigr\rceil+1\ <\ \frac{n_{\rm end}-n}{p}+2 ,
```

with equality in the middle inequality when $n\equiv-1\pmod p$. In particular, joint large-prime numerator conditions for distinct primes, whether in the same band $(n/2,n]$ or across bands such as $(n/3,n/2]$, impose no restriction beyond the product of single-prime conditions.

*Proof.* By `GF-47` Theorem 3.2(2), the $q$-primary components of $x_{n'}+2^{n'-n}\delta$ for $q\nmid M$ equal those of $x_{n'}$, and the $p$-component for $p\mid M$ is that of $x_{n'}$ plus $2^{n'-n}\bar a_p/p$. Since $p$ is odd and $p^2>n'$, `GF-47` Lemma 3.3 with $J=1$ gives $ps_{n'}\equiv2^{n'-m}s_m\pmod p$ with $m=\lfloor n'/p\rfloor<p$. If $p\nmid A_m$, the $p$-component of $x_{n'}$ has exact denominator $p$, and the translate keeps denominator $p$ iff $2^{n'-m}s_m+2^{n'-n}\bar a_p\not\equiv0$, i.e. $\bar a_p\not\equiv-2^{n-m}s_m$. This condition depends on $n'$ only through the band $m$. If $p\mid A_m$, the $p$-component of $x_{n'}$ vanishes, and it stays zero iff $\bar a_p=0$. CRT makes the conditions independent across primes. For the count, write $n=qp+r$ with $0\le r\le p-1$ and $L=n_{\rm end}-n\ge1$. Then $\lvert B_p(W)\rvert=\lfloor(r+L-1)/p\rfloor+1\le\lfloor(L-2)/p\rfloor+2=\lceil(L-1)/p\rceil+1\le(L+p-2)/p+1<L/p+2$. $\square$

*Both hypotheses are needed.* The earlier bound $\lvert B_p(W)\rvert\le(n_{\rm end}-n)/p+1$ is false: $n=9$, $n_{\rm end}=11$, $p=5$ gives $B_5(W)=\{1,2\}$, so $\lvert B_5(W)\rvert=2>\frac75$ (here band $2$ is a drop band, $A_2=5$). With no drop band, $n=13$, $n_{\rm end}=15$, $p=7$ gives $\operatorname{Excl}_7(W)=\{4,6\}$, so $\lvert\operatorname{Excl}_7(W)\rvert=2>\frac97$. Oddness is also needed, because the band law $ps_{n'}\equiv2^{n'-m}s_m$ fails at $p=2$. For $n=2$, $n_{\rm end}=3$, $M=2$: $s_1=1$, $s_2=\frac52$, $B_2(W)=\{1\}$, $A_1=1$ and $\operatorname{Excl}_2(W)=\{0\}$, so the statement would admit $\bar a_2=1$; but $x_2+\frac12\equiv0$ has denominator $1\ne Q_2=2$. Theorem 1.2 uses only primes $p>X_i$, which are odd, and the band count $\lvert B_p(W)\rvert<\rho n/p+2$. The script certifies all three counterexamples.

`GF-47`'s two-element sets $F_p$ are the case $B_p(W)=\{1,2\}$. The script checks the band law and the exact admissible sets against brute force over all $a\bmod p$ for $168$ prime–window pairs ($n\in\{60,90,131\}$, $\rho\in\{\frac32,2,3\}$), together with the band-count bound. It checks the band-count formula, its bound and the equality case on every odd-prime window with $3\le n<80$ and $n_{\rm end}\le2n+1$, and the CRT product count on $12$ prime pairs.

**Insertion law and twisted sums are blind (Paper proof).** Inside a reset-free block, every translate satisfies the prime insertion law $\tilde s_p-2\tilde s_{p-1}=\frac1p$ exactly. Twisted Weyl sums satisfy $\sum_{n'\in W}e(h\tilde x_{n'})=\sum_{n'\in W}e(h2^{n'}y)+O(\lvert h\rvert\sum_{n'\in W}T_{n'})$ with $y=\ln2+2^{-n}\hat\delta$ (`GF-47` Lemma 3.1). Thus consecutive-prime insertion correlations and twisted sums see only the doubling orbit of the real number $y$. By Lemma 1.1, the prime-local data are fully decoupled. **The only global coupling left is the real approximation $y\approx\ln2$**, and Theorems 1.3–1.4 exploit exactly this.

### 1.2 Geometric resets up to the information ratio

**Theorem 1.2 (full-denominator resets for every $\rho<1+1/\ln2$; Paper proof + PNT; Finite certificate).** Let $1<\rho<1+1/\ln2=2.442695\ldots$. For all sufficiently large $n_0$ and $n_{i+1}=\lfloor\rho n_i\rfloor$, there are states $\tilde x_n\in\mathbb Q/\mathbb Z$ ($n\ge n_0$) with:

1. reduced denominator exactly $Q_n$ for every $n\ge n_0$;
2. $\tilde x_n=x_n+2^{n-n_i}\delta_i$ on $[n_i,n_{i+1})$, where $\operatorname{den}\delta_i$ divides $M_i=\prod p$ over the primes $p\in(X_i,n_i]$, $X_i=2\rho n_i/\ln n_i$, that meet no drop band in the block;
3. the BBP recurrence at every step except at the resets, of which there are at most $\log(N/n_0)/\log\rho+O(1)$ up to $N$;
4. $\|\tilde x_n\|\to0$.

*Proof.* Fix $i$, write $n=n_i$ and $W=[n,\lfloor\rho n\rfloor)$. For $p>X_i$ we have $p$ odd and $p^2>\rho n$ for large $n$, so Lemma 1.1 applies with $\lvert B_p(W)\rvert<\rho n/p+2$.

*Size of the modulus.* A drop prime divides some $A_m$ with $m\le\rho n/X_i\le\frac12\ln n$. Since $\lvert A_m\rvert\le2^mL_m\le8^m$ (elementary $L_m\le4^m$), at most $\sum_{m\le\ln n}3m=O(\log^2n)$ primes are lost, which is $O(\log^3n)$ bits. By PNT, $\log_2M_i=(\vartheta(n)-\vartheta(X_i))/\ln2-O(\log^3n)=(1-o(1))\,n/\ln2$.

*Sieve.* Let $\tau_i=-\{2^n\ln2\}$ and $a_0=\operatorname{round}(M_i\tau_i)$. In an interval of $K=n^3$ consecutive integers, Lemma 1.1 excludes at most

```math
\sum_{p\mid M_i}\Bigl(\frac{\rho n}{p}+2\Bigr)\Bigl(\frac{K}{p}+1\Bigr)\le K\Bigl(\rho n\sum_{p>X_i}\frac1{p^2}+2\sum_{X_i<p\le n}\frac1p\Bigr)+O(n\log\log n)=K\bigl(\tfrac12+o(1)\bigr),
```

using $\sum_{p>X}p^{-2}=(1+o(1))/(X\ln X)$ and $\sum_{X_i<p\le n}1/p=\ln\frac{\ln n}{\ln X_i}+o(1)=o(1)$ (Mertens; PNT). So there is an admissible $a$ with $\lvert a-a_0\rvert\le n^3$.

*Smallness.* With $y_i=\ln2+2^{-n}a/M_i$ and $n'\in W$, $\tilde x_{n'}\equiv2^{n'}y_i-T_{n'}$, and

```math
\|\tilde x_{n'}\|\le2^{(\rho-1)n}\,\frac{n^3+1}{M_i}+\frac1{n'}=2^{\,(\rho-1-(1-o(1))/\ln2)\,n+O(\log n)}+\frac1{n'}\longrightarrow0 .
```

Items 1–3 hold by construction and Lemma 1.1. $\square$

*Finite certificate.* The script constructs the block $[1000,2000)$ of ratio $2$. It uses $132$ primes in $(150,1000]$ with no drop band, $\log_2M=1182$, and $T_{1000}$ to precision about $2^{-1389}$. The target residue $a_0$ itself is admissible. All $1000$ states have reduced denominator exactly $Q_{n'}$, the recurrence holds at all $999$ inner steps, and $\|\tilde x_{n'}\|\le1/n'+2^{-30}$ throughout (`[finite]`: $\max n'\|\tilde x_{n'}\|=0.99900$). The ratio $2$ exceeds both `GF-47`'s $\frac32$ and its top-band limit $1+\frac1{2\ln2}=1.72134\ldots$.

*Consequence for Track B.* The full-denominator blocks of ratio $\rho_{\rm info}=1+1/\ln2=2.442695\ldots$ that *B* §5 treats as hypothetical exist for every $\rho<\rho_{\rm info}$. *B* Theorem 5.1(1)–(2) applies to them verbatim. Prime-centered Hankel windows inside such a block have $\alpha<\frac{\rho-1}{\rho+1}<0.4191<\alpha_*$, so they impose no lower bound.

### 1.3 A translate-robust dyadic measure

**Theorem 1.3 (Paper proof + PNT; Finite certificate).** For every $\eta>0$, every $M\ge M_0(\eta)$ and every rational $x$ whose reduced denominator divides $L_M$,

```math
\bigl\lvert2^M\ln2-x\bigr\rvert\ \ge\ 2^{-(5.178813\ldots+\eta)M}.
```

*Proof.* Follow *B* Theorem 4.5. Choose a prime $p=\frac{M}{1-\alpha}(1+o(1))$ with $\alpha\downarrow\alpha_*=0.442847\ldots$, put $r=p-M+1$, and let $c_j$, $P_{r-1}^{(0,M)}(3)=\sum_jc_j2^j$ and $I_{M,r-1}>0$ be as in *B* Theorem 4.3, so that $I_{M,r-1}=2^MP(3)\ln2-\sum_{j<r}c_js_{M+j}$. Set

```math
\widetilde\Lambda:=xP(3)-\sum_{j<r}c_js_{M+j}=I_{M,r-1}-\bigl(2^M\ln2-x\bigr)P(3).
```

Every $s_{M+j}$ ($j<r$) has denominator dividing $L_{M+r-1}=L_p$, and $\operatorname{den}x\mid L_M\mid L_p$, so $L_p\widetilde\Lambda\in\mathbb Z$. For an integer $m$, *B* Theorem 4.3(4) gives $v_p(\Lambda_{M,r}(m))=-1$. Since $p>M$, $x-m$ is $p$-integral and $\widetilde\Lambda=\Lambda_{M,r}(m)+(x-m)P(3)$, so $v_p(\widetilde\Lambda)=-1$. Hence $\widetilde\Lambda\ne0$ and $\lvert\widetilde\Lambda\rvert\ge1/L_p$. The analytic estimates of *B* Lemma 4.4 ($L_pI_{M,r-1}\le\frac12$ eventually, $P(3)\le e^{g(\alpha)p}$) do not involve $x$, so the chain of *B* Theorem 4.5 gives $\lvert2^M\ln2-x\rvert\ge(1-L_pI)/(L_pP(3))\ge2^{-(5.178813+\eta)M}$. $\square$

*Remark (one-dimensional form).* The proof works directly with the one-dimensional Jacobi–Padé form $\widetilde\Lambda$ of *B* Theorem 4.3 and needs no Hankel determinant. The two arithmetic facts are $\operatorname{den}x\mid L_M\mid L_p$, which gives $L_p\widetilde\Lambda\in\mathbb Z$, and $p>M$, which gives $p\nmid L_M$ and hence $x\in\mathbb Z_{(p)}$ and $v_p(\widetilde\Lambda)=v_p(\Lambda_{M,r}(m))=-1$. In the equivalent $r\times r$ Hankel formulation with $m_{M+k}=2^kx$, the row operations $\mathrm{row}_i-2\,\mathrm{row}_{i-1}$ cancel $x$ in every row $i\ge1$. So $x$ survives only in row $0$, where $L_p$ already clears $\operatorname{den}x$.

*Comparison.* Applying $\mu(\ln2)\le3.5745539$ (Marcovecchio 2009) to $q=2^M\operatorname{den}x\le2^ML_M$ gives only $\lvert2^M\ln2-x\rvert\ge2^{M-(3.5745539+o(1))(1+1/\ln2)M}=2^{-(7.7316+o(1))M}$. The prime-centered forms already pay $L_p\supseteq L_M$, so the shift costs nothing. The script verifies $L_p\widetilde\Lambda\in\mathbb Z$ and $v_p(\widetilde\Lambda)=-1$ on $3924$ exact forms ($11\le p\le157$; denominators $1$, $L_M$, $Q_M$ and $L_M/\gcd(L_M,6)$; four shifts each). On the $142$ of $259$ windows where the enclosure gives $L_pI_{M,r-1}<1$, it also verifies the lower bound itself.

### 1.4 Uniform reset countermodels need $\Theta(\log N)$ resets

**Theorem 1.4 (Paper proof + PNT).** Let $(\tilde x_n)_{n\ge n_0}$ be a uniform reset countermodel with $\limsup\|\tilde x_n\|<\frac14$ whose reset states satisfy $\operatorname{den}(\tilde x_{n_i})\mid L_{n_i}$ (for instance, exact denominators $Q_{n_i}$). Then

```math
n_{i+1}\le\bigl(\mu_2^{\rm Hankel}+o(1)\bigr)\,n_i=\bigl(6.178813\ldots+o(1)\bigr)\,n_i ,
```

so the number of resets up to $N$ is at least $\bigl(1/\log_2\mu_2^{\rm Hankel}-o(1)\bigr)\log_2N=(0.3806-o(1))\log_2N$.

*Proof.* By `GF-47` Lemma 3.1, on $[n_i,n_{i+1})$ we have $\tilde x_k=x_k+2^{k-n_i}\delta_i$ with $\delta_i=\tilde x_{n_i}-x_{n_i}$. Its denominator divides $\operatorname{lcm}(Q_{n_i},\operatorname{den}\tilde x_{n_i})\mid L_{n_i}$. Then $\tilde x_k\equiv2^ky_i-T_k$ with $y_i=\ln2+2^{-n_i}\hat\delta_i$. Fix $c>0$ with $\|\tilde x_k\|\le\frac14-c$ for large $k$. Since $T_k<1/(k+1)$, eventually $\|2^ky_i\|<\frac14$ for all $k\in[n_i,n_{i+1})$. When $\|t\|<\frac14$ we have $\|2t\|=2\|t\|$, so $\|2^{n_i}y_i\|=2^{-(n_{i+1}-1-n_i)}\|2^{n_{i+1}-1}y_i\|<2^{-(n_{i+1}-n_i)-1}$. Thus $\lvert2^{n_i}\ln2-x\rvert<2^{-(n_{i+1}-n_i)-1}$ for $x=A-\hat\delta_i$, whose denominator divides $L_{n_i}$. Theorem 1.3 gives $n_{i+1}-n_i+1\le(5.178813+o(1))n_i$.

*Finitely many resets.* The argument above assumes that a next reset $n_{i+1}<\infty$ exists. Suppose instead that no reset occurs after some $n_i$. Then $\tilde x_k=x_k+2^{k-n_i}\delta_i\equiv2^ky_i-T_k$ for all $k\ge n_i$, and there is a $K$ with $\|2^ky_i\|<\frac14$ for every $k\ge K$. Hence $\|2^Ky_i\|=2^{-(N-K)}\|2^Ny_i\|<2^{-(N-K)-2}$ for every $N\ge K$, so $2^Ky_i\in\mathbb Z$. Then $\ln2=y_i-2^{-n_i}\hat\delta_i$ is rational, a contradiction. So every uniform reset countermodel has infinitely many resets, and the bound applies to each consecutive pair. $\square$

**Corollary 1.5 (exact order; answer to `GF-47` Open Question 4 for uniform barriers).** For uniform reset countermodels with full-denominator resets:

1. $O(\log N)$ resets suffice (`GF-47` Thm 3.6; Thm 1.2 with any ratio $\rho<1+1/\ln2=2.442695\ldots$);
2. $\Omega(\log N)$ resets are necessary (Thm 1.4);
3. the supremum $\rho_{\max}$ of admissible geometric ratios satisfies $1+1/\ln2\le\rho_{\max}\le\mu_2^{\rm Hankel}$, so in particular $2.4426<\rho_{\max}\le6.1789$.

In particular, **no barrier in the sense of `GF-47` Theorem 3.6 exists with $o(\log N)$ resets.** The coupling between adjacent blocks that defeats sparse resets is the requirement that every block translate $y_i$ be a $2^{-(n_{i+1}-n_i)}$-good approximation of $2^{n_i}\ln2$ by a fraction with denominator dividing $L_{n_i}$.

*Limits of F1 (Objective 4).* Corollary 1.5 constrains countermodels, not the digits of $\ln2$. Non-uniform countermodels (empirical measures tending to $\delta_0$ along a subsequence while blocks contain many medium runs) with $o(\log N)$ resets are not excluded, because Theorem 1.3 controls only single long runs. **$D^+(\ln2;2)\le0.9999$ remains Open.** This is consistent with *B* Theorem 5.1(3): single-block lower bounds see only linear runs.

---

## 2. F2: partition constants beyond the `GF-45` transitions

### 2.0 The transfer from approximation to digits

**Lemma 2.0 (reciprocal run transfer; Paper proof).** Let $y>0$ be irrational, $Z=1/y$, and let $N\ge0$ satisfy $b^NZ\ge1$ (for instance $Z\ge1$).

1. If $Z$ has a constant run of length $L$ after position $N$, then there is an integer $A$ with $1\le A\le(b-1)b^NZ+(b-1)$ and $\lvert Ay-(b-1)b^N\rvert\le(b-1)\,y\,b^{-L}$.
2. If $\|(b-1)b^kZ\|<\frac1{2b}$ for every $k\in[N,N+L]$ (no escape), then with $A\ge1$ the integer nearest to $(b-1)b^NZ$, $\lvert Ay-(b-1)b^N\rvert<\frac12y\,b^{-L-1}$.

*Proof.* (1) If $d_{N+1}=\dots=d_{N+L}=d$, then $b^NZ=I+\frac{d(1-b^{-L})}{b-1}+b^{-L}\theta$ with $I=\lfloor b^NZ\rfloor\ge1$ and $\theta\in[0,1)$. So $(b-1)b^NZ=A+\eta$ with $A=(b-1)I+d\ge b-1\ge1$ and $\lvert\eta\rvert\le(b-1)b^{-L}$. Multiply by $y$, using $Zy=1$. (2) While $\|u\|<\frac1{2b}$, $\|bu\|=b\|u\|$. Iterating from $k=N$ to $N+L$ gives $\|(b-1)b^NZ\|<b^{-L-1}/2$, and $A\ge1$ because $(b-1)b^NZ\ge1$; multiply by $y$. $\square$

*The hypothesis $b^NZ\ge1$ is needed.* For $b=2$, $y=100\sqrt2$, $N=1$ and $L=6$ we have $Z=\sqrt2/200<2^{-7}$, so $d_2=\dots=d_7=0$ and the construction gives $A=0$. No integer $A\ge1$ works, because $\lvert Ay-2\rvert\ge y-2>y/64$. In every application below, $Z=P_b=\prod_{j\ge1}(1-b^{-j})^{-1}>1$, so $b^NP_b>1$ for every $N\ge0$.

So every lower bound $\lvert Ay-B\rvert\ge\phi(A)$ valid for all integers $A\ge1$ and $B$ bounds both the runs and the escape gaps of $1/y$. Only lower bounds valid for **all** $B$ are used below; the special value $B=(b-1)b^N$ is not exploited.

### 2.1 Explicit $q$-Padé forms for Euler's product

Let $C_n(x)=\prod_{j=n+1}^{2n}(x-b^j)=\sum_{i=0}^nc_ix^i$. For $n\ge1$ define

```math
Q_n=\sum_{r=0}^{n}(-1)^r\,b^{\,r(n+1)+r^2}\left[{n\atop r}\right]_b\frac{D_n}{D_r},\qquad P_n=(-1)^n\sum_{k=0}^{n}(-1)^k\left[{n\atop k}\right]_bD_{2n-k},\qquad\lambda_n=Q_nE_b-P_n .
```

**Theorem 2.1 (Paper proof + External input: Euler's identity; Finite certificate).** For every base $b\ge2$ and every $n\ge1$:

1. $Q_n,P_n\in\mathbb Z$, and $\lambda_n=D_n\sum_{k\ge2n+1}T_k$ with
   ```math
   T_k=(-1)^k\,b^{\,n(3n+1)/2-nk}\,\frac{D_{k-n-1}}{D_{k-2n-1}\,D_k}\qquad(k\ge2n+1).
   ```
2. $\frac{13}{15}E_b\,b^{-e_n}\le\lvert\lambda_n\rvert\le2\,b^{-e_n}$ with $e_n=\frac{(3n+2)(n+1)}2$, and $\lambda_n<0$.
3. $\lvert Q_n\rvert\le3b^{2n^2+n}$, and $\lvert Q_n\rvert\ge\frac12b^{2n^2+n}$ for $n\ge2$.
4. $Q_nP_{n+1}-P_nQ_{n+1}\ne0$ for every $n\ge1$.

*Proof.* Put $F(z)=(z;q)_\infty$. Euler's identity (External input; Andrews, *The Theory of Partitions*, Cor. 2.2) gives

```math
F(z)=\sum_{k\ge0}\frac{(-1)^kq^{k(k-1)/2}}{(q;q)_k}z^k\quad(z\in\mathbb C),\qquad F(q^j)=\frac{(q;q)_\infty}{(q;q)_{j-1}}=\frac{E_b}{(q;q)_{j-1}}\quad(j\ge1).
```

*The combination.* Sum $c_iF(q^{n+1-i})$ over $0\le i\le n$. On one side this is $E_b\,\alpha_n$ with $\alpha_n=\sum_ic_i/(q;q)_{n-i}$. On the other side, by absolute convergence, it is $\sum_{k\ge0}T_k$ with

```math
T_k=\frac{(-1)^kq^{k(k-1)/2+(n+1)k}}{(q;q)_k}\,C_n(q^{-k})=\frac{(-1)^k\,C_n(b^k)}{b^{nk}D_k},
```

because $\sum_ic_iq^{-ik}=C_n(b^k)$. Since $C_n(b^k)=0$ for $n<k\le2n$, the series splits into $k\le n$ and $k\ge2n+1$.

*Integrality.* For $k\le n$, $C_n(b^k)=(-1)^nb^{nk}\prod_{j=n+1}^{2n}(b^{j-k}-1)=(-1)^nb^{nk}D_{2n-k}/D_{n-k}$. Hence

```math
T_k=(-1)^{n+k}\frac{D_{2n-k}}{D_{n-k}D_k}=(-1)^{n+k}\left[{n\atop k}\right]_b\prod_{j=n+1}^{2n-k}(b^j-1)\in\mathbb Z,
```

and $\sum_{k\le n}T_k=P_n/D_n$, which is an integer; the theorem uses the integer $P_n$. By the $q$-binomial theorem, $c_i=(-1)^r\,b^{r(n+1)+r(r-1)/2}[{n\atop r}]_b$ with $r=n-i$. With $1/(q;q)_r=b^{r(r+1)/2}/D_r$ this gives $D_n\alpha_n=Q_n$. For $k\ge2n+1$, $C_n(b^k)=b^{n(3n+1)/2}D_{k-n-1}/D_{k-2n-1}$, which gives the displayed $T_k$ and proves (1): $Q_nE_b-P_n=D_n(E_b\alpha_n-\sum_{k\le n}T_k)=D_n\sum_{k\ge2n+1}T_k$.

*(2)* For $k\ge2n+1$,

```math
\frac{\lvert T_{k+1}\rvert}{\lvert T_k\rvert}=\frac{b^{k-n}-1}{b^n(b^{k-2n}-1)(b^{k+1}-1)}\le\frac{2}{b^{k+1}-1}\le\frac2{15},
```

using $(b^{k-n}-1)/(b^{k-2n}-1)\le b^n\cdot\frac b{b-1}$. The signs alternate, and $\operatorname{sgn}T_k=(-1)^k$. So $\lambda_n$ has the sign of $T_{2n+1}<0$ and $\frac{13}{15}\lvert D_nT_{2n+1}\rvert\le\lvert\lambda_n\rvert\le\lvert D_nT_{2n+1}\rvert$. Now $D_nT_{2n+1}=-b^{-(n^2+n)/2}D_n^2/D_{2n+1}$. Writing $D_k=b^{k(k+1)/2}\pi_k$ with $\pi_k=\prod_{j\le k}(1-b^{-j})\in[E_b,1)$ gives $D_n^2/D_{2n+1}=b^{-(n+1)^2}\pi_n^2/\pi_{2n+1}$. Finally $\pi_n^2/\pi_{2n+1}=\pi_n/\prod_{j=n+1}^{2n+1}(1-b^{-j})\in[E_b,2]$, because the last product is at least $1-b^{-n}/(b-1)\ge\frac12$.

*(3)* The term $r=n$ of $Q_n$ is exactly $(-1)^nb^{2n^2+n}$. For $r<n$, use $[{n\atop r}]_b\le P_b\,b^{r(n-r)}$ and $D_n/D_r\le b^{(n(n+1)-r(r+1))/2}$. Each such term is then at most $P_bb^{f(r)}$, where $f(r)=r(2n+1)+\frac{n^2+n}2-\frac{r^2+r}2$, $f(n)=2n^2+n$ and $f(n)-f(r)=\frac{(n-r)(3n+1-r)}2\ge(n-r)(n+1)$, because $3n+1-r\ge2n+2$ for $r\le n-1$. Summing the geometric series over $n-r\ge1$ gives $\bigl\lvert\lvert Q_n\rvert-b^{2n^2+n}\bigr\rvert\le b^{2n^2+n}P_b/(b^{n+1}-1)$. Since $P_b\le P_2<3.463$, the ratio is at most $P_2/3<1.16$ for $n\ge1$, which gives $\lvert Q_n\rvert\le3b^{2n^2+n}$. For $n\ge2$ it is at most $P_2/(2^3-1)<0.4948<\frac12$, which gives $\lvert Q_n\rvert\ge\frac12b^{2n^2+n}$, for every $b\ge2$.

*(4)* For every $n\ge1$, $Q_nP_{n+1}-P_nQ_{n+1}=Q_{n+1}\lambda_n-Q_n\lambda_{n+1}$. Since $n+1\ge2$, (2)–(3) give $\lvert Q_{n+1}\lambda_n\rvert/\lvert Q_n\lambda_{n+1}\rvert\ge\frac{13E_b}{180}\,b^{7(n+1)}$, using $f(n+1)-f(n)+e_{n+1}-e_n=7n+7$. With $E_b\ge E_2>0.2887$ and $b^{7(n+1)}\ge2^{14}$, this is greater than $\frac{13\cdot0.2887}{180}\,2^{14}>341>1$. So the determinant is nonzero for every $b\ge2$ and every $n\ge1$, including $n=1$. As an independent check, the script also computes the determinant exactly for $n\le9$, $b\in\{2,3,5,10\}$, and for $n\in\{1,2\}$, $2\le b\le17$. $\square$

This is the $[n/n]$-type Padé construction for the first-order $q$-difference equation $F(z)=(1-z)F(qz)$, evaluated at the lattice point $z=q^{n+1}$, where the roots $q^{-j}$ ($n<j\le2n$) of $C_n$ make the numerator side integral. Its quality is $\sigma=\lim\log\lvert\lambda_n\rvert^{-1}/\log\lvert Q_n\rvert=\frac{3/2}{2}=\frac34$.

### 2.2 The irrationality exponent of Euler's product

**Theorem 2.2 (Paper proof; Finite certificate).** For every $b\ge2$, $\mu(E_b)=\mu(P_b)\le\frac73$. Explicitly, let $A\ge1$ and $B$ be integers, and let $n=n_A\ge2$ be minimal with $b^{e_n}\ge4A$. Then

```math
\lvert AE_b-B\rvert\ \ge\ \frac{1}{6\,b^{\,2(n+1)^2+(n+1)}},\qquad\text{and, if }n\ge3,\qquad \lvert AE_b-B\rvert\ \ge\ \frac16\,(4A)^{-4/3}\,b^{-17n/3-3},
```

where $n<\frac16\bigl(1+\sqrt{1+24\log_b(4A)}\bigr)$ in the second case.

*Proof.* For $m\in\{n,n+1\}$, $A\lvert\lambda_m\rvert\le2Ab^{-e_m}\le\frac12$. By Theorem 2.1(4) the pairs $(Q_n,P_n)$ and $(Q_{n+1},P_{n+1})$ are not proportional, so $AP_m-BQ_m\ne0$ for some such $m$. Then $1\le\lvert AP_m-BQ_m\rvert=\lvert Q_m(AE_b-B)-A\lambda_m\rvert$ gives $\lvert AE_b-B\rvert\ge\frac1{2\lvert Q_m\rvert}\ge\frac1{6b^{f(n+1)}}$. If $n\ge3$, minimality gives $b^{e_{n-1}}<4A$ with $e_{n-1}=\frac{(3n-1)n}2$, and $f(n+1)=2n^2+5n+3=\frac43e_{n-1}+\frac{17n}3+3$. Since $n=O(\sqrt{\log A})$, $\lvert AE_b-B\rvert\ge A^{-4/3-o(1)}$, so $\mu(E_b)\le1+\frac43$. The exponent is invariant under $x\mapsto1/x$. $\square$

*Remark (prior art; the bound $\frac73$ is not new).* Irrationality of $E_b$ is classical: it already follows from the unbounded pentagonal gaps. **The irrationality exponent bound $\mu(E_b)\le\frac73$ is published prior art, due to P. Bundschuh** (*Invent. Math.* **9** (1969/70), 175–184). Leinonen, Leinonen and Matala-aho (2016) call it "a record holding result proved already by Bundschuh" for $\prod_{k\ge1}(1-d^{-k})$. The arithmetic of the $q$-exponential product and of related $q$-series was developed further by Bundschuh (*Portugal. Math.* **33** (1974), 1–17, Tschakaloff series), Bundschuh–Väänänen (*Compositio Math.* **91** (1994), 175–199) and Matala-aho (*J. Number Theory* **128** (2008), 1–16). Padé approximation to $q$-exponential functions also goes back to P. Borwein (1988). For approximations restricted to the shape $d^s/N$, **L. Leinonen, M. Leinonen and T. Matala-aho** (*Int. J. Number Theory* **12** (2016), 287–303; arXiv:1412.4115) improve $\frac73$ to

```math
2+\frac{1}{3+2\sqrt3}=1+\frac{2}{\sqrt3}=2.1547005\ldots .
```

This is close to the shape $(b-1)b^N/A$ produced by the run transfer of Lemma 2.0(1); for $b=2$ it is exactly $d^s/N$ with $d=2$ (see §10, Question 3). We read the abstract and introduction of arXiv:1412.4115 and the bibliographic records of the other papers, not their full proofs. Which of the later papers re-derive $\frac73$ for $E_b$ itself is therefore not asserted here.

**What Track F adds.** Theorems 2.1–2.2 are a self-contained explicit $q$-Padé reproof of $\frac73$, with explicit integers, explicit constants, and a nonvanishing determinant proved for every $b\ge2$ and $n\ge1$. The repository's contribution is the unconditional transfer to the digits of $P_b=1/E_b$ (Corollary 2.3): linear runs, at least $(0.818\ldots-o(1))\log_2N$ transitions and escapes, and the discrepancy gap $1-D_N(P_b;b)\gg_b(\log N)/N$. It also proves the exact barriers of §§2.4–2.5: the $\frac38N^2$ pinning of $b$-power approximants, the $\log N$ ceiling of run methods, and the $b$-adic Ridout reformulation (Prop. 2.6). Any priority claim for these digit consequences is provisional.

### 2.3 Linear runs and logarithmic transitions for $P_b=1/E_b$

**Corollary 2.3 (Paper proof).** For every $b\ge2$ and $N\ge1$:

1. every constant run of $P_b$ after position $N$, and every escape-free stretch $[N,N+L]$, has
   ```math
   L\ \le\ \tfrac43N+\tfrac{17}3\,n_A+C_b\ \le\ \tfrac43N+\tfrac{17\sqrt6}{9}\sqrt N+O_b(1)\ \le\ \tfrac43N+4.63\sqrt N+O_b(1);
   ```
2. every window $(N,\frac73N+O_b(\sqrt N)]$ contains a transition and an escape. Hence $\chi_N(P_b)\ge\bigl(\frac1{\ln(7/3)}-o(1)\bigr)\ln N=(0.818\ldots-o(1))\log_2N$, and the number of escapes before $N$ is at least as large;
3. $1-D_N(P_b;b)\gg_b(\log N)/N$.

*Proof.* By Lemma 2.0 with $y=E_b$ (its hypothesis $b^NP_b\ge1$ holds for every $N\ge0$ because $P_b>1$), $1\le A\le b^{N+1}P_b$ and $\lvert AE_b-B\rvert\le(b-1)E_bb^{-L}$ for an integer $B$. Theorem 2.2 then gives $L\le\log_b(6(b-1)E_b)+\frac43\log_b(4A)+\frac{17n_A}3+3$, with $\log_b(4A)\le N+1+\log_b(4P_b)$ and $n_A\le\frac16(1+\sqrt{1+24(N+1+\log_b4P_b)})$. Iterating (2) from a fixed $n_0$ reaches $N$ only after at least $\log(N/n_0)/\log(\frac73+o(1))$ steps. For (3), use [GF-32, Lemma 5.3]: $1-D_N(z;b)\ge\frac25\min_{c_0\in F_b}M_N(z-c_0;b)-\frac1N$. Each escape contributes at least $1/(2b(b-1))$ to $NM_N$ for every fixed point $c_0$. $\square$

**Comparison with `GF-45` E4.** E4 proved runs $\le\frac38N^2+O(N)$ (pentagonal truncations), $\gg\log\log N$ transitions and $1-D_N\gg(\log\log N)/N$. Corollary 2.3 replaces the quadratic run bound by a linear one, an exponential improvement in the transition count. $P_b$ thereby joins the logarithmic class of $X_{b,m}$ ($m\ge3$, `GF-45` E3), $\pi$, $e$, $\zeta(3)$ and $\ln2$ (§4.3). The same bound holds for every Möbius image $(aE_b+c)/(a'E_b+c')$ with integer entries and nonzero determinant, for instance $E_b$, $P_b-1$ and $1/(1-E_b)$.

### 2.4 Why $b$-power approximants are pinned at $N^2$

**Proposition 2.4 (Paper proof; Finite certificate).** Let $g_k$ run through the generalized pentagonal numbers $0,1,2,5,7,12,15,\ldots$. For every integer $g\ge1$, with $g_{k+1}$ the least pentagonal number exceeding $g$,

```math
\|b^gE_b\|\ \ge\ \tfrac12\,b^{-(g_{k+1}-g)}\ \ge\ \tfrac12\,b^{-\sqrt{8g/3}-2}.
```

Consequently, any certificate that bounds $\lvert AE_b-B\rvert$ from below by comparison with approximants of denominator $b^g$ needs $\sqrt{8g/3}+O(1)\ge\log_bA$, that is $g\ge\frac38(\log_bA-O(1))^2$, and yields at best runs $\le(\frac38+o(1))N^2$ for $P_b$. `GF-45` E4's constant $\frac38$ is optimal in this class.

*Proof.* With $E_b=\sum_k\varepsilon_kb^{-g_k}$ ($\varepsilon_k=\pm1$, Euler's pentagonal theorem), the terms with $g_k\le g$ become integers after multiplication by $b^g$. The remaining sum is $\varepsilon_{k+1}b^{g-g_{k+1}}(1+\theta)$ with $\lvert\theta\rvert\le2b^{-(g_{k+2}-g_{k+1})}\le\frac12$, because $g\ge1$ forces $g_{k+1}\ge2$ and every pentagonal gap after $2$ is at least $2$. So no small cases need separate treatment; the script checks $g<400$, $b\in\{2,3,10\}$ independently. Put $u=b^{-(g_{k+1}-g)}(1+\theta)\in[\frac12b^{-(g_{k+1}-g)},\frac32b^{-(g_{k+1}-g)}]$; then $\|b^gE_b\|=\min(u,1-u)$. If $u\le\frac12$, this is $u\ge\frac12b^{-(g_{k+1}-g)}$. The wrap-around $u>\frac12$ happens only for $b=2$, $g_{k+1}-g=1$ and $\theta>0$. Then $1-u=\frac12(1-\theta)\ge\frac14=\frac12\cdot2^{-1}$, so the bound still holds. Consecutive gaps satisfy $g_{k+1}-g_k\le2i+1\le\sqrt{8g/3}+2$. In the comparison lemma of §2.2, the condition $A\lvert b^gE_b-p\rvert\le\frac12$ forces the stated size of $g$, and the bound returned is $\frac1{2b^g}$. $\square$

So the isolation mechanism is pinned at scale $N^2$ by the $\sqrt g$ spacing of the pentagonal numbers: $E_b$ is $b$-adically badly approximable at scale $b^{-O(\sqrt g)}$. Positive quality ($\sigma=\frac34$) needs denominators coprime to $b$, such as the cyclotomic products $D_n=\prod_d\Phi_d(b)^{\lfloor n/d\rfloor}$ in $Q_n$. This is exactly the mechanism of Theorem 2.1.

### 2.5 The ceiling of run methods, and what lies beyond $\log N$

**Proposition 2.5 (sharpness of run transfer; Paper proof; Finite certificate).** Let $\lambda>1$ and $t_k=\lceil\lambda^k\rceil$. Let $w_\lambda$ be the binary number whose digits switch exactly at the distinct positions $t_k$. Every constant run of $w_\lambda$ after position $n\ge t_0-1$ has length $\le(\lambda-1)(n+1)+1$, and $\chi_N(w_\lambda)=\log_\lambda N+O(1)$.

*Proof.* A run inside $[t_k,t_{k+1})$ starting after $n\ge t_k-1$ has length $\le t_{k+1}-t_k\le(\lambda-1)t_k+1$. $\square$

Hence a uniform linear run bound $L(n)\le(\lambda-1)n+O(1)$ can never yield more than $\log_\lambda N+O(1)$ transitions. The transfer "runs $\le(\mu-1)n$ implies $\chi_N\ge\log_\mu N-O(1)$" (Cor. 2.3, Thm 4.1) is sharp in order and in constant. **For $X_{b,m}$ the ceiling was already reached by `GF-45` E3** (runs $\le\frac m{m-2}n$), and for $P_b$ it is reached by Corollary 2.3. Any further asymptotic gain needs sublinear runs.

**Proposition 2.6 (exact reformulation of the next step; Paper proof; the property itself is Open).** The following are equivalent:

1. every constant run of $P_b$ after position $N$ has length $o(N)$;
2. $\|(b-1)b^NP_b\|\ge b^{-o(N)}$;
3. $\min\{\lvert AE_b-(b-1)b^N\rvert:\ A\in\mathbb Z\}\ge b^{-o(N)}$.

Each of them implies $\chi_N(P_b)/\log N\to\infty$.

*Proof.* (2)$\Leftrightarrow$(3) by multiplying by $E_b$ or by $P_b$ (both bounded). (2)$\Rightarrow$(1) by Lemma 2.0(1). (1)$\Rightarrow$(2): suppose $\|(b-1)b^NP_b\|<b^{-L}$. Put $t=\{b^NP_b\}\in[0,1)$ and let $d\in\{0,\dots,b-1\}$ be the integer nearest to $(b-1)t$. Then $t=d/(b-1)+\eta$ with $\lvert\eta\rvert<b^{-L}/(b-1)$, and $b^Lt=d\,\frac{b^L-1}{b-1}+\bigl(\frac d{b-1}+b^L\eta\bigr)$, where the bracket lies in $[0,1)$. For $1\le d\le b-2$ this holds because the bracket lies in $\bigl(\frac{d-1}{b-1},\frac{d+1}{b-1}\bigr)$. The two wrap-around cases also hold: $d=0$ forces $\eta\ge0$ (as $t\ge0$), and $d=b-1$ forces $\eta<0$ (as $t<1$). So in every case the digits $d_{N+1},\dots,d_{N+L}$ all equal $d$, a run of length $L$. Sublinear runs put a transition within $o(n)$ of every position $n$, whence the transition count. $\square$

For algebraic irrationals the analogue of (3) is Ridout's theorem (External input). For $E_b$ a $q$-analogue would be needed, for instance Padé forms whose denominators are a power of $b$ times $b^{o(n^2)}$. Proposition 2.4 shows that no such forms come from the pentagonal side. Whether they exist is **Open**.

*Mahler's functional equation for $X_{b,m}$.* The identity $(1-1/b)X_{b,m}=X_{b^m,m}$, that is $(b-1)b^NX_{b,m}=b^{N+1}X_{b^m,m}$, turns a run of length $L$ of $X_{b,m}$ after $N$ into a run of $0$s or $(b-1)$s of length at least $L-1$ of $X_{b^m,m}$ (written in base $b$) after position $N+1$, that is, starting at digit $N+2$. Iterating $j$ times reproduces exactly the `GF-45` E3 approximants $A_k/b^{s_k}$ with $A_k=\prod_{i<k}(b^{m^i}-1)$. So the functional equation adds no information beyond E3, and by Proposition 2.5 E3's linear run bound already saturates every run method.

---

## 3. F3: the equality boundary $d=r$ and the cube $C_1(3)^3$

### 3.1 Depth recursion and the rational-tail inequality

**Proposition 3.1 (Paper proof; Finite certificate).** With $U_d(z)=\sum_{p\nmid i}z^{i^d}$,

```math
C_s(z)=U_d(z)+p^{-s}\,C_s\bigl(z^{p^d}\bigr),\qquad C_s(z)^d=\sum_{j=0}^{d}\binom dj\,p^{-sj}\,U_d(z)^{d-j}\,C_s\bigl(z^{p^d}\bigr)^j .
```

Hence $p$-power denominators of $c_m$ arise only from representations that use the rescaled copy, and $e_M\le s\log_pM$. Indeed, a representation $m=x_1^d+\dots+x_d^d\le M$ contributes $p^{-s\,v_p(x_1\cdots x_d)}$, and $v_p(x_1\cdots x_d)\le\log_p(x_1\cdots x_d)\le\log_pM$, because AM–GM gives $x_1\cdots x_d\le M/d\le M$.

*Proof.* Split $i$ according to $v_p(i)$; then expand the $d$-th power. The script checks the first identity coefficientwise up to degree $4161$ for the flagship cube. $\square$

**Theorem 3.2 (rational-tail inequality; Paper proof).** Let $v\ge1$ be an integer with $vX\in\mathbb Z$, and put $v'_M=v/\gcd(v,B^M)$ (if $X=u/v$ in lowest terms, $v'_M=\operatorname{den}(B^MX)$). Then for every $M\ge0$,

```math
T_M\ \ge\ \frac1{\operatorname{lcm}\bigl(v'_M,\,p^{e_M}\bigr)}\ \ge\ \frac1{v\,p^{e_M}} .
```

So $\inf_Mp^{e_M}T_M=0$ implies $X\notin\mathbb Q$.

*Proof.* $B^MX=B^M(vX)/v$ has denominator dividing $v'_M$, and $R_M\in\mathbb Z+p^{-e_M}\mathbb Z$. So $T_M=B^MX-R_M$ is a positive rational whose denominator divides $\operatorname{lcm}(v'_M,p^{e_M})$. $\square$

This is `GF-46` Theorem 1.3(1) at **zero residue precision $h=0$**. That is the denominator-only information: $\lfloor R_M\rfloor$ and the numerator $A_M$ of $\{R_M\}=A_M/p^{e_M}$ are discarded, and (1.1) reads $T_{\max}<g_0/(v'_Mp^{e_M})=1/\operatorname{lcm}(v'_M,p^{e_M})$. Theorem 3.3 identifies which multi-packet certificates reduce to this test and which do not.

### 3.2 Multi-packet collapse

**Theorem 3.3 (multi-packet collapse; Paper proof; Finite certificate).** Let $S$ be a finite set of shifts with $M^*=\max S$. Suppose that for each $M\in S$ one knows the exact prefix $R_M$ and a tail bound $\tau_M\ge T_M$, and that all $c_m\ge0$. Define the propagated bound

```math
\tau^*=\min_{M\in S}\Bigl(B^{M^*-M}\tau_M-\sum_{i=M+1}^{M^*}c_iB^{M^*-i}\Bigr)\ \ge\ T_{M^*}.
```

Fix $v\ge1$ and put $v'=v/\gcd(v,B^{M^*})$.

1. *(Exact prefixes: interval collapse.)* The joint information $\{(R_M,\tau_M)\}_{M\in S}$ says exactly that $X\in(R_{M^*}B^{-M^*},(R_{M^*}+\tau^*)B^{-M^*}]$, so it is equivalent to the single packet $(R_{M^*},\tau^*)$. It excludes $vX\in\mathbb Z$ if and only if
   ```math
   v\,\tau^*B^{-M^*}\ <\ 1-\bigl\{v\,R_{M^*}B^{-M^*}\bigr\}
   ```
   (when $vR_{M^*}B^{-M^*}\in\mathbb Z$ the right side is $1$). Collective cancellation across adjacent packets, whether through determinants or joint numerators, adds nothing to this one packet.
2. *(Denominator-only certificates, $h=0$.)* Suppose the certificate feeds into its final test only the depth $p^{e_{M^*}}$ and the bound $\tau^*$. It discards $\lfloor R_{M^*}\rfloor$ and the numerator $A_{M^*}$ of $\{R_{M^*}\}=A_{M^*}/p^{e_{M^*}}$, which is the information of `GF-46` Theorem 1.3(1) at $h=0$. Then it excludes $vX\in\mathbb Z$ if and only if $\tau^*<1/\operatorname{lcm}(v',p^{e_{M^*}})$. In this class the best multi-packet certificate is the test of Theorem 3.2 at $M^*$, and it can succeed only if $T_{M^*}\le\tau^*<1/\operatorname{lcm}(v',p^{e_{M^*}})$.
3. *(Low-residue certificates.)* Suppose instead the certificate keeps $A_{M^*}\bmod p^h$ for some $1\le h\le e_{M^*}$, still discarding $\lfloor R_{M^*}\rfloor$. Then it excludes $vX\in\mathbb Z$ only if $\tau^*<p^{\,h-e_{M^*}}$, and only if $\tau^*<p^{\,h-e_{M^*}}/v$ when $\gcd(v,pB)=1$. In particular $h\le(1-\varepsilon)e_{M^*}$ requires $\tau^*<p^{-\varepsilon e_{M^*}}$.

*Proof.* (1) Packet $M$ says $X\in J_M=(R_MB^{-M},(R_M+\tau_M)B^{-M}]$. Since $c_m\ge0$, the left endpoints $R_MB^{-M}$ increase with $M$. Hence $\bigcap_MJ_M=(R_{M^*}B^{-M^*},\min_M(R_M+\tau_M)B^{-M}]$, and $(R_M+\tau_M)B^{-M}=(R_{M^*}+B^{M^*-M}\tau_M-\sum_{i=M+1}^{M^*}c_iB^{M^*-i})B^{-M^*}$ by the exact relation $R_{M^*}=B^{M^*-M}R_M+\sum_{i=M+1}^{M^*}c_iB^{M^*-i}$. An interval $(a,a+t]$ meets $v^{-1}\mathbb Z$ iff the least integer $\lfloor va\rfloor+1$ above $va$ is at most $v(a+t)$, that is, iff $vt\ge1-\{va\}$. (2) By (1), the tail data of all packets amount to $0<T_{M^*}\le\tau^*$. With the denominator-only information at $M^*$, `GF-46` Theorem 1.3(1) at $h=0$ has $r_{\min}=g_0=\gcd(v',p^{e_{M^*}})$, so (1.1) reads $\tau^*<g_0/(v'p^{e_{M^*}})=1/\operatorname{lcm}(v',p^{e_{M^*}})$. The case $e_{M^*}=0$ is the same computation with $A_{M^*}=0$, and the threshold there is $1/v'$. The true tail is the smallest admissible bound. (3) By `GF-46` Theorem 1.3(1), exclusion holds iff $v'p^{e_{M^*}}\tau^*<r_{\min}(v',A_0,h)$, and $r_{\min}\le g_0p^h\le v'p^h$ with $g_0=\gcd(v',p^{e_{M^*}-h})$, which equals $1$ when $\gcd(v,pB)=1$. $\square$

*(2)–(3) do not extend to certificates that keep more information.* An earlier draft of this theorem claimed that *every* multi-packet certificate needs $T_{M^*}<1/\operatorname{lcm}(\operatorname{den}(B^{M^*}X),p^{e_{M^*}})$. That is false, as two exact counterexamples on the flagship cube show (certified in the script with outward-rounded tail enclosures):

- *Exact prefix beats both $h=0$ and $h=e$.* Take $M^*=91$, $v=10$, $v'=5$. Here $e_{91}=3$ and $c_{92}=2$, so $T_{91}\ge\frac12>\frac1{135}=1/\operatorname{lcm}(5,27)$, and the $h=0$ test fails for every admissible tail bound. With $\{R_{91}\}=\frac{22}{27}$, $r_{\min}(5,22,3)=25<5\cdot27\cdot T_{91}$, so the full-residue test fails too. Yet $R_{91}4^{-91}=0.0156278\ldots$ and $\tau_{91}4^{-91}<4^{-90}$, so criterion (1) excludes $10X\in\mathbb Z$. In general, if $X\notin v^{-1}\mathbb Z$, one exact-prefix packet excludes $v$ as soon as $\tau_MB^{-M}<\operatorname{dist}(X,v^{-1}\mathbb Z)$. For this reason exact-prefix certificates carry no structural obstruction: excluding every $v$ this way is equivalent to irrationality itself.
- *Full residue beats $h=0$ even with $\lfloor R\rfloor$ unknown.* Take $M^*=126$, $v=4$, $v'=1$. Here $e_{126}=3$, $\{R_{126}\}=\frac1{27}$ and $c_{127}=3$, so $T_{126}\in[0.75,0.797]$. The $h=0$ threshold is $\frac1{27}<T_{126}$. `GF-46` Theorem 1.3(1) at $h=e=3$ has $r_{\min}(1,1,3)=26$, and $27\,T_{126}<26$, so it excludes $4X\in\mathbb Z$.

Earlier depths combined with exact innovations can also pin residues of $A_{M^*}$. For example, if $e_{M^*-1}=0$ then $\{R_{M^*}\}=\{c_{M^*}\}$. So a certificate that keeps the depths at all $M\in S$ together with the innovations can be a residue certificate at $M^*$ rather than an $h=0$ one. A multi-packet certificate belongs to class (2) or (3) according to the information it actually feeds into the test at $M^*$, not according to how many packets it uses.

The script verifies the propagated identity $T_{M'}=B^{M'-M}T_M-\sum_{i=M+1}^{M'}c_iB^{M'-i}$ exactly (on truncated series) for $33$ pairs. It checks the interval criterion of (1) against brute force, the $h=0$ threshold $\min_{p\nmid A}\min\{T>0:v'(A/p^e+T)\in\mathbb Z\}=1/\operatorname{lcm}(v',p^e)$ for $p\in\{3,5\}$, $e\le4$, $v'\le60$, and the low-residue bound $r_{\min}/(v'p^e)\le p^{h-e}$. It also certifies both counterexamples above.

### 3.3 A finite exclusion certificate for $C_1(3)^3$

**Theorem 3.4 (Finite certificate).** For the flagship cube, $C_1(3)^3\ne u/v$ for every integer $u$ and every integer $1\le v<V^*$, where $\lfloor V^*\rfloor=6636192071781020039363335\approx6.636\times10^{24}$.

*Certificate.* At $M=3331$, which lies in $S_3^+$, the exact prefix has depth $e_{3331}=6$. The next element of $S_3^+$ is $3377$, so the $45$ integers in between are not sums of three positive cubes. The tail enclosure is $T_{3331}\le\sum_{j\le160}c_{3331+j}4^{-j}+2(3331+162)4^{-160}$, using $c_m\le m$. Then $V^*=1/(3^6\,T_{3331}^{\rm hi})$, and Theorem 3.2 excludes every $v<V^*$. The script evaluates this exclusion at all $4000$ shifts $M\le4000$ and keeps the best. This is a finite statement and does not prove irrationality.

*Finite measurement.* There are $74$ shifts $M\le4000$ with $e_M=0$, including $M=1,\dots,8$ and the `GF-46` drop $M=1268$ (re-verified). The support density of $(c_m)$ up to $4000$ is $0.119$.

### 3.4 The exact exponent obstruction

Write $m'_M$ for the least element of $S_3^+$ exceeding $M$, $\gamma_M=m'_M-M$ for the gap, and $H_M=\sum_{j\ge0}c_{m'_M+j}B^{-j}$ for the post-gap mass, so that $T_M=B^{-\gamma_M}H_M$.

**Theorem 3.5 (gap–mass–depth reduction; Paper proof + External input for (3)).**

1. *(Sufficient.)* If $\limsup_M\bigl(\gamma_M\log B-\log H_M-e_M\log p\bigr)=+\infty$, then $C_s(3)^3$ is irrational.
2. *(Necessary for denominator-only and low-residue truncation proofs.)* Denominator-only ($h=0$) truncation certificates (Theorem 3.3(2)) exclude $vX\in\mathbb Z$ for every $v\ge1$ **if and only if** condition (1) holds. Suppose instead that at each shift used the certificate keeps $A_M\bmod p^{h_M}$ with $h_M\le(1-\varepsilon)e_M$ (Theorem 3.3(3), the low-residue class of `GF-46` Theorem 1.3(2)). Then excluding every $v$ requires $\limsup_M(\gamma_M\log B-\log H_M-\varepsilon e_M\log p)=+\infty$. Neither statement applies to residue-boosted proofs that use the exact fractional parts $\{R_M\}$, such as `GF-46` Theorem 1.3(3) on Ghidelli's gaps. Nor does either apply to exact-prefix certificates (Theorem 3.3(1)), for which excluding every $v$ is equivalent to irrationality itself. The counterexamples after Theorem 3.3 ($M^*=91$, $v=10$; $M^*=126$, $v=4$) show that such certificates can succeed where the $h=0$ test fails.
3. *(Where the exponents stand.)* Unconditionally, $(3/m'_M)^s\le c_{m'_M}\le H_M\le O(M)$ and $e_M\le s\log_pM$. Ghidelli (External input) gives infinitely many gaps with $\gamma_M\gg(\log M)^{1/2}/(\log\log M)^2$. Phase 21 Prop. D gives $e_M\ge(s-o(1))\log_pM$ at density one. Consider the generic regime $H_M\asymp1$, $e_M\sim s\log_pM$. There condition (1) requires $\gamma_M\ge(\frac{s}{\log B}-o(1))\log M$ along a subsequence, and its low-residue analogue requires $\gamma_M\ge(\frac{\varepsilon s}{\log B}-o(1))\log M$. Either way this is gap exponent $1$ in $\log M$, against the unconditional exponent $\frac12$. Otherwise it requires an anomaly correlated with the gap: depth collapse $e_M\le(\frac{\log B}{\log p}-\varepsilon)\gamma_M$, or post-gap mass concentrated on highly $p$-divisible representations ($H_M\le M^{-s+o(1)}$).

*Proof.* (1) $p^{e_M}T_M=\exp(-(\gamma_M\log B-\log H_M-e_M\log p))$; apply Theorem 3.2. (2) If (1) holds, then $\inf_Mp^{e_M}T_M=0$. For each $v$, Theorem 3.2's test with a sufficiently accurate tail bound succeeds at some $M$, since $\operatorname{lcm}(v'_M,p^{e_M})\le vp^{e_M}$. Conversely, take $v$ coprime to $pB$. Then $v'_M=v$ and $\operatorname{lcm}(v,p^{e_M})=vp^{e_M}$, so by Theorem 3.3(2) excluding $vX\in\mathbb Z$ needs a shift $M$ with $p^{e_M}T_M<1/v$. Letting $v\to\infty$ through such integers gives $\inf_Mp^{e_M}T_M=0$. Since each $p^{e_M}T_M$ is positive, this forces the $\limsup$ in (1) to be $+\infty$. For the low-residue class, Theorem 3.3(3) with $\gcd(v,pB)=1$ gives $T_M<p^{h_M-e_M}/v\le p^{-\varepsilon e_M}/v$ at the shift used, and the same limit gives $\inf_Mp^{\varepsilon e_M}T_M=0$. (3) $c_{m'}\ge\min p^{-s\,v_p(xyz)}\ge(xyz)^{-s}\ge(m'/3)^{-s}$ by AM–GM; the remaining facts are quoted. $\square$

**Status.** Irrationality of $C_1(3)^3$ (and of $C_s(3)^3$, $s\ge1$) remains **Open**. For denominator-only and low-residue truncation proofs, the obstruction is exactly the exponent deficit $\frac12$ in (3), or the absence of a gap-correlated depth or mass anomaly. Residue-boosted routes are not obstructed by (2). An example is the phase condition $\limsup_k\{-vR_{M_k}\}B^{K_k}/(\log T_k)^C=\infty$ on Ghidelli's gaps (`GF-46` Theorem 1.3(3), Conditional), which remains a live, unproved route. *Heuristic only (not evidence):* if $S_3^+$ behaved like a Poisson set of density $\delta\approx0.1$, its largest gaps near $M$ would be about $\log M/\log\frac1{1-\delta}\approx9.5\log M$, far above the threshold $\frac1{\log4}\log M\approx0.72\log M$.

---

## 4. F4: algebraic irrationals and the famous constants

### 4.1 Möbius run transfer

**Theorem 4.1 (Paper proof; standard).** Let $x$ be irrational with $\mu(x)\le\mu<\infty$, and let $y=(ax+c)/(a'x+c')$ with integer entries and $ac'-a'c\ne0$. In every base $b$:

1. every constant run of $y$ after $N$, and every escape-free stretch $[N,N+L]$, has $L\le(\mu-1+o(1))N$;
2. $\chi_N(y)\ge(\frac1{\log\mu}-o(1))\log N$, there are as many escapes, and $1-D_N(y;b)\gg(\log N)/N$.

*Proof.* $\mu(y)=\mu(x)$. A run gives $\lvert y-A/((b-1)b^N)\rvert\le b^{-N-L}$ (Lemma 2.0(1) without the reciprocal), and then $b^{-N-L}\ge((b-1)b^N)^{-\mu-o(1)}$. Escapes and the discrepancy follow as in Corollary 2.3. $\square$

By Proposition 2.5, this is the exact ceiling of every argument that uses only a finite irrationality exponent.

### 4.2 What the algebraic equation imposes on signed orbits

**Proposition 4.2 (bounded-remainder form; Paper proof; Finite certificate).** Let $D\ge2$ be a nonsquare and $y>0$ real. Put $x_N=\lfloor2^Ny\rfloor$, $d_{N+1}=x_{N+1}-2x_N\in\{0,1\}$ and $E_N=D\,4^N-x_N^2$. Then:

1. $E_{N+1}=4E_N-d_{N+1}(4x_N+d_{N+1})$ identically, for every $y$;
2. $y=\sqrt D$ if and only if $\sup_N\lvert E_N\rvert2^{-N}<\infty$, and then $1\le E_N<2^{N+1}\sqrt D+1$;
3. for $y=\sqrt D$, $d_{N+1}=1$ if and only if $E_N>x_N$.

The analogue for $\varphi$, with $F_N=x_N^2-2^Nx_N-4^N\in(-2^{N+2},0)$, is certified as well.

*Proof.* (1) Expand $(2x_N+d)^2$. (2) $E_N=(2^N\sqrt D-x_N)(2^N\sqrt D+x_N)$. If $y=\sqrt D$, the first factor lies in $(0,1)$ and $E_N\in\mathbb Z_{\ge1}$. Conversely $\lvert E_N\rvert\le C2^N$ forces $\lvert\sqrt D-x_N2^{-N}\rvert\le C/(\sqrt D\,2^N)\to0$. (3) $d=1\iff(2x_N+1)^2\le4D4^N\iff4E_N\ge4x_N+1$. $\square$

*Consequences (Objective 4).* The equation $\alpha^2=D$ acts on the digit sequence only through the condition that the digit-driven integer recursion (1) stays within $O(2^N)$. The block-doubling identity of `GF-47` Prop. 4.2 is its two-block iterate. By `GF-47` Lemma 4.1 ($\frac13(\chi_N-1)\le\sigma_N\le\chi_N$), signed-digit/NAF weight carries the same information as transitions. So algebraic equations give **strictly stronger** digit restrictions than every finite-$\mu$ method, namely runs $o(N)$ and $\chi_N/\log N\to\infty$ (`GF-40`, via Ridout). This separation is sharp by Proposition 2.5. But it comes only from the $p$-adic Subspace/Ridout input, not from the equation's effect on signed orbits or Toeplitz/Hankel determinants. **No new lower bound for $\sigma_N(\sqrt2)$ or $\chi_N(\sqrt2)$ is claimed.** The positivity and determinant tools of *B* do not apply, because $\sqrt2$, $\sqrt3$ and $\varphi$ have no BBP-type positive-moment representation.

### 4.3 Ledger, consistent with Track B's B7

| Constant | Approximation input | Run bound after $N$ | Transitions $\chi_N$ | *B* §7 Hankel status |
| --- | --- | --- | --- | --- |
| $\sqrt2,\sqrt3,\varphi$ | Ridout (External input) | $o(N)$ | $\chi_N/\log N\to\infty$ (`GF-40`) | not applicable (no BBP form) |
| $e$ | $\mu(e)=2$ (External input) | $(1+o(1))N$ | $\ge(1-o(1))\log_2N$ | $v_p=-mr$; B3 and positivity fail |
| $\pi$ | $\mu\le7.103205\ldots<7.1033$ (Zeilberger–Zudilin 2020) | $(6.1033+o(1))N$ | $\ge(\frac1{\ln7.1033}-o(1))\ln N$ | $v_p=-r$ (proved); denominator balance fails on the $M=0$ benchmark (*B* Thm 7.1(3): Heuristic for prime-centered $M>0$) |
| $\zeta(3)$ | $\mu\le5.513891$ (Rhin–Viola 2001) | $(4.513891+o(1))N$ | $\ge(\frac1{\ln5.5139}-o(1))\ln N$ | $v_p=-3r$ (proved); positivity fails (*B* Thm 7.3(3a), Paper proof); balance fails on the $M=0$ benchmark (*B* Thm 7.3(3b): Heuristic for prime-centered $M>0$) |
| $\ln2$ | $\mu\le3.5745539$ (Marcovecchio 2009); self-contained binary $5.1788$ (*B* Thm 4.5; Thm 1.3) | $(2.5746+o(1))N$ | $\ge(\frac1{\ln3.5746}-o(1))\ln N$ | full B1–B4 structure; reset barriers (§1) |
| $E_b$, $P_b$ | $\mu\le\frac73$ (Bundschuh 1970; **Thm 2.2, self-contained reproof**) | $\frac43N+O(\sqrt N)$ | $\ge(\frac1{\ln(7/3)}-o(1))\ln N$ | — |
| $X_{b,m}$, $m\ge3$ | `GF-45` E3 approximants | $\frac m{m-2}N+O(1)$ | $\gg\log N$ | — |
| $X_{b,2}$ | $\mu=2$ (Bugeaud 2011; Phase 23) | $(1+o(1))N$ | $\ge(1-o(1))\log_2N$ | — |

All entries except the $E_b$/$P_b$ row and the self-contained $\ln2$ entries rest on external Diophantine theorems. Upper bounds on $\mu$ are rounded outward (up), so the run and transition entries remain valid. The *B* §7 column keeps Track B's evidence labels: the $M=0$ linear-balance comparisons for $\pi$ and $\zeta(3)$ are benchmarks, not proofs of failure for prime-centered windows. Every non-algebraic row is capped at order $\log N$ by Proposition 2.5. **No benchmark status changes.**

---

## 5. Limitation ledger (Objective 4)

| Barrier | Statement | Where |
| --- | --- | --- |
| CRT decoupling | Same-band and cross-band large-prime data for $\ln2$ form an exact CRT product; prime-local joint conditions add nothing | Lemma 1.1 |
| Insertion / twisted-sum blindness | Insertion law $\tilde s_p-2\tilde s_{p-1}=\frac1p$ and twisted Weyl sums see only the block orbit of $y_i$ | §1.1 |
| Uniform versus non-uniform resets | $\Theta(\log N)$ resets are exact for uniform countermodels; non-uniform ones with $o(\log N)$ resets are open | Thm 1.2, Thm 1.4 |
| $N^2$ pinning | $b$-power approximants of $E_b$ cannot beat $(\frac38+o(1))N^2$ runs | Prop. 2.4 |
| Run-method ceiling | Uniform linear run bounds give at most $\log_\lambda N+O(1)$ transitions, and this is attained | Prop. 2.5 |
| Mahler functional equation | Reproduces `GF-45` E3 exactly; no further information | §2.5 |
| Multi-packet collapse | Joint packets are equivalent to one packet with the propagated tail; denominator-only ($h=0$) certificates then reduce exactly to Thm 3.2's test, low-residue ones to $\tau^*<p^{-\varepsilon e_{M^*}}$. Exact-prefix and full-residue certificates are not limited this way | Thm 3.3 |
| Gap–mass–depth deficit | Denominator-only and low-residue ($h\le(1-\varepsilon)e_M$) truncation proofs for $C_1(3)^3$ need gap exponent $1$; the unconditional exponent is $\frac12$. Residue-boosted routes (`GF-46` Thm 1.3(3)) are not excluded | Thm 3.5 |
| Bounded remainder | $\alpha^2=D$ acts on digits only through an $O(2^N)$ integer recursion | Prop. 4.2 |

---

## 6. External inputs and hypothesis checks

| Input | Statement used | Where |
| --- | --- | --- |
| Euler (1748); Andrews, *The Theory of Partitions*, Cor. 2.2 and Ch. 1 (pentagonal number theorem) | $(z;q)_\infty=\sum_k(-1)^kq^{k(k-1)/2}z^k/(q;q)_k$ for $\lvert q\rvert<1$; pentagonal number theorem | Thm 2.1, Prop. 2.4 ($q=1/b$, inside the disk of convergence) |
| Prime number theorem, Mertens | $\vartheta(x)\sim x$, $\sum_{p>X}p^{-2}\sim1/(X\ln X)$, $\sum_{X<p\le n}1/p=\ln\frac{\ln n}{\ln X}+o(1)$ | Thm 1.2; via *B* in Thms 1.3–1.4 |
| Track B (repository) | Thm 4.3 (forms $\Lambda_{M,r}$, $v_p=-1$), Lemma 4.4 and Thm 4.5 (analytic estimates, $\mu_2^{\rm Hankel}=6.178813$), Thm 5.1 | Thms 1.3, 1.4, §1.2 |
| `GF-47` (repository) | Lemma 3.1, Thm 3.2(2), Lemma 3.3 (band law), Thm 3.6, Lemma 4.1, Prop. 4.2 | §1, §4.2 |
| `GF-32` Lemma 5.3, `GF-45` E3/E4, `GF-46` Thm 1.3 (repository) | finite discrepancy inequality; partition approximants; exact one-gap + low-residue characterization (1.1) with $r_{\min}(Q',A_0,h)$, its $h=0$ case, the low-residue barrier (2) and the residue-boosted criterion (3) | Cor. 2.3, §2.5, Thms 3.2–3.5 |
| Bundschuh (1970); Leinonen–Leinonen–Matala-aho (2016) | prior art: $\mu(E_b)\le\frac73$; restricted-shape exponent $1+2/\sqrt3$ for approximations $d^s/N$ | §2.2 remark, §7, §10 Question 3 only (no theorem here depends on them) |
| Ghidelli (arXiv:1910.05076; JLMS 2020); Phase 21 Prop. D | gaps in $S_3^+$ of length $\gg(\log M)^{1/2}/(\log\log M)^2$; density-one depth growth | Thm 3.5(3) only |
| Ridout (1957); Euler/continued fraction for $e$; Zeilberger–Zudilin (2020); Rhin–Viola (2001); Marcovecchio (2009); Bugeaud (2011) | Diophantine exponents | §4.3 ledger and the comparison in §1.3 only |

---

## 7. Prior art and attribution

- **$\mu(E_b)\le\frac73$ is prior art.** The bound is due to P. Bundschuh (*Invent. Math.* **9** (1969/70), 175–184), as stated explicitly by Leinonen–Leinonen–Matala-aho (2016) for $\prod_{k\ge1}(1-d^{-k})$. The arithmetic of $q$-exponential values was developed further by Bundschuh (*Portugal. Math.* **33** (1974), 1–17), Bundschuh–Väänänen (*Compositio Math.* **91** (1994), 175–199) and Matala-aho (*J. Number Theory* **128** (2008), 1–16). For approximations restricted to the shape $d^s/N$, L. Leinonen, M. Leinonen and T. Matala-aho (*Int. J. Number Theory* **12** (2016), 287–303) improve $\frac73$ to $2+\frac1{3+2\sqrt3}=2.1547\ldots$. Other $q$-Padé background: P. Borwein (1988) for the $q$-exponential, and Bézivin (1988) for linear independence. Theorems 2.1–2.2 are a self-contained explicit instance of this method, and **no novelty is claimed for $\mu(E_b)\le\frac73$**. The bibliographic data above were checked against Numdam (Compositio), arXiv:1412.4115 (text and DOI 10.1142/S1793042116500172) and the reference lists of citing papers; the IJNT page range is as reported in the Track F review. The 1970 attribution and the restricted-shape exponent were read in arXiv:1412.4115 itself. The theorem statements of Bundschuh (1974), Bundschuh–Väänänen (1994) and Matala-aho (2008) were not re-read here.
- **Track F's F2 contribution** is the explicit self-contained Padé derivation (explicit integers $Q_n,P_n$, explicit constants, nonvanishing for all $b\ge2$, $n\ge1$) together with its unconditional transfer to the digits of $P_b$. That transfer gives runs $\le\frac43N+4.63\sqrt N+O_b(1)$, at least $(0.818\ldots-o(1))\log_2N$ transitions and as many escapes, and $1-D_N(P_b;b)\gg_b(\log N)/N$ (Cor. 2.3). It also gives the exact barriers: the $\frac38N^2$ pinning of $b$-power approximants (Prop. 2.4), the $\log N$ ceiling of run methods (Prop. 2.5), and the $b$-adic Ridout reformulation (Prop. 2.6).
- Prime-centered Padé forms for $\ln2$ and the reset countermodels are repository results (*B*, `GF-47`). The translate-robust measure (Thm 1.3), the reset thresholds (Thms 1.2 and 1.4), the explicit ratio-2 block, the $P_b$ digit consequences (Cor. 2.3), the $N^2$ pinning (Prop. 2.4), multi-packet collapse with its $h=0$/low-residue scope (Thm 3.3) and the finite exclusion (Thm 3.4) are new in this repository. Priority is provisional: a literature search that finds nothing does not establish priority.

---

## 8. Standing objectives advanced

| Result | Objective ([`docs/research-objectives.md`](../../docs/research-objectives.md)) |
| --- | --- |
| Thm 2.1, Thm 2.2, Cor. 2.3 | **Objective 3** (exact transition and escape counts, finite-$N$ discrepancy gaps for $P_b$ and $E_b$) |
| Lemma 1.1, Thms 1.2–1.4 | **Objective 4** (exact thresholds for reset barriers; answer to `GF-47` OQ4 for uniform barriers) and **Objective 3** (Thm 1.3) |
| Props 2.4–2.6, Thm 3.3, Thm 3.5, Prop. 4.2 | **Objective 4** (rigorous limitations of isolation, run, multi-packet and signed-orbit methods) |
| Thm 3.4 | **Objective 3** (finite exclusion of small rational values; a finite certificate, not irrationality) |

---

## 9. Reproduction and exact verification

```sh
python -B scripts/phase26_classical_nonlinear.py
```

Standard library only. The script exits `0` in about 17 s on Windows with **179,335 exact assertions** (`F1` 109,874; `F2` 8,295; `F3` 22,951; `F4` 38,215). The file contains no floating-point literal, and its only `float()` call formats one isolated `[finite]` measurement outside every assertion:

- **F2 (`[exact]`, `[encl]`):** $q$-binomial coefficient identity and vanishing of $C_n$ ($b\in\{2,3,5,10\}$, $n\le10$). Closed forms, integrality, signs and ratio bounds of $T_k$; $P_n=D_n\sum_{k\le n}T_k$ and $Q_n=D_n\alpha_n$ ($n\le8$). Enclosure check of $\lambda_n=Q_nE_b-P_n=D_n\rho_n$, the two-sided size bounds, the deviation bound $\lvert\lvert Q_n\rvert-b^{2n^2+n}\rvert\le b^{2n^2+n}P_b/(b^{n+1}-1)$, $\lvert Q_n\rvert\ge\frac12b^{2n^2+n}$ for $n\ge2$, and the sign ($n\le9$). The analytic constants of Thm 2.1(3)–(4): $P_2<3.463$, $P_2/7<\frac12$, $E_2>0.2887$, $\frac{13\cdot0.2887}{180}2^{14}>341$, $f(n)-f(r)\ge(n-r)(n+1)$, and the exponent $7(n+1)$. Nonvanishing of consecutive determinants ($n\le9$ for $b\in\{2,3,5,10\}$; $n\in\{1,2\}$ for $2\le b\le17$). The Lemma 2.0 counterexample and $P_b>1$. The measure chain for $402$ explicit integers $A$. Prop. 2.4 for $g<400$, $b\in\{2,3,10\}$, including the next-gap bound $g_{k+2}-g_{k+1}\ge2$. The run-of-length-$L$ step of Prop. 2.6, wrap-around cases included. Certified digits of $P_2$ and $P_3$ (1500 digits) against the run bound.
- **F1 (`[exact]`):** band law, exact admissible sets and band-count bound against brute force ($168$ odd-prime–window pairs). The band-count formula, the bound $\lceil(n_{\rm end}-n-1)/p\rceil+1$ and its equality case on all odd-prime windows with $3\le n<80$, $n_{\rm end}\le2n+1$. The three counterexamples to the original Lemma 1.1 ($p=5$, $p=7$, $p=2$). CRT product counts ($12$ prime pairs). The full ratio-2 block $[1000,2000)$ (exact denominators, recurrence, smallness). $3924$ translate-robust Padé forms ($L_p\widetilde\Lambda\in\mathbb Z$, $v_p=-1$), with the lower bound checked on the $142$ windows where $L_pI<1$.
- **F3 (`[exact]`):** depth recursion to degree $4161$; prefixes, depths ($3^{e_M}\le M$) and tail enclosures for all $M\le4000$; the best exclusion certificate; $33$ propagated-tail identities. The exact-prefix interval criterion against brute force, the $h=0$ threshold $1/\operatorname{lcm}(v',p^e)$, and the low-residue bound $r_{\min}/(v'p^e)\le p^{h-e}$. The two Theorem 3.3 counterexamples ($M^*=91$, $v=10$; $M^*=126$, $v=4$). $q_{1268}=1$.
- **F4 (`[exact]`):** remainder recursion, digit rule and bounded remainder for $\sqrt2,\sqrt3,\sqrt5$ ($N<3000$) and $\varphi$ ($N<2000$); ceiling witnesses for $\lambda\in\{\frac73,\frac32,5\}$.
- **Isolated `[finite]` measurements:** longest observed run ratios and transition counts of $P_2$ and $P_3$; data of the ratio-2 block ($132$ primes, $\log_2M=1182$, $a=a_0$, $\max n'\|\tilde x_{n'}\|=0.99900$); the exclusion bound and the shifts with zero depth. These bear on no limit.

---

## 10. Open questions

1. **Optimal reset ratio.** Determine $\rho_{\max}\in[1+1/\ln2,\,\mu_2^{\rm Hankel}]\subset[2.4426,6.1789]$ for uniform full-denominator reset countermodels of $\ln2$. Do non-uniform countermodels with $o(\log N)$ resets exist?
2. **$b$-adic Ridout property for Euler's product.** Prove $\min_A\lvert AE_b-(b-1)b^N\rvert\ge b^{-o(N)}$ (Prop. 2.6), or any sublinear run bound for $P_b$ or $X_{b,m}$. This is the only route beyond $\log N$ transitions allowed by Prop. 2.5.
3. **Sharper $\mu(E_b)$ and restricted shapes.** Asymmetric root sets $\{b^j:a<j\le a+n\}$ or cyclotomic prime-factor refinements (in the style of Rukhadze and Hata) may lower $\frac73$. A more direct route goes through the restricted shape. Lemma 2.0(1) only needs lower bounds for $\lvert E_b-(b-1)b^N/A\rvert$, and Leinonen–Leinonen–Matala-aho (2016) bound approximations of shape $d^s/N$ with exponent $1+2/\sqrt3=2.1547\ldots$. For $b=2$ the shape is exactly $2^N/A$. Taking their theorem as an External input (not re-proved here), Lemma 2.0 would give runs of $P_2$ of length $\le(2/\sqrt3+o(1))N=(1.1547\ldots+o(1))N$, which lowers $\frac43$. For $b\ge3$ the extra factor $b-1$ lies outside their shape, and whether their method covers $(b-1)d^s/N$ is open here. Either way only constants change, not the order $\log N$ of the transition count (Prop. 2.5).
4. **$C_1(3)^3$.** Find infinitely many three-cube gaps with $\gamma_M\log B-\log H_M-e_M\log p\to\infty$ (Thm 3.5), for instance gaps of length $(\frac1{\log4}+\varepsilon)\log M$ with bounded post-gap mass. Alternatively, pursue a residue-boosted route outside the scope of Thm 3.5(2), such as phase control of $\{-vR_{M_k}\}$ on Ghidelli's gaps (`GF-46` Thm 1.3(3)).
5. **Unchanged.** $D^+<1$, simple normality or $K_b$ membership for $\ln2$, $\pi$, $e$, $\zeta(3)$, $\sqrt2$, $E_b$, $P_b$, $X_{b,m}$; $\sigma_N(\sqrt2)\gg N^\delta$.

---

## References

- G. E. Andrews, *The Theory of Partitions*, Addison-Wesley, 1976.
- J.-P. Bézivin, Indépendance linéaire des valeurs des solutions transcendantes de certaines équations fonctionnelles, *Manuscripta Math.* **61** (1988), 103–129.
- P. Borwein, Padé approximants for the $q$-elementary functions, *Constr. Approx.* **4** (1988), 391–402.
- Y. Bugeaud, On the rational approximation to the Thue–Morse–Mahler numbers, *Ann. Inst. Fourier* **61** (2011), 2065–2076.
- P. Bundschuh, Ein Satz über ganze Funktionen und Irrationalitätsaussagen, *Invent. Math.* **9** (1969/70), 175–184.
- P. Bundschuh, Verschärfung eines arithmetischen Satzes von Tschakaloff, *Portugal. Math.* **33** (1974), 1–17.
- P. Bundschuh and K. Väänänen, Arithmetical investigations of a certain infinite product, *Compositio Math.* **91** (1994), 175–199.
- D. Ghidelli, On rational approximation of a geometric sum of cubes, arXiv:1910.05076; and the cubic gap theorem, *J. London Math. Soc.* (2020).
- L. Leinonen, M. Leinonen and T. Matala-aho, On approximation measures of $q$-exponential function, *Int. J. Number Theory* **12** (2016), 287–303, doi:10.1142/S1793042116500172; arXiv:1412.4115.
- R. Marcovecchio, The Rhin–Viola method for $\log 2$, *Acta Arith.* **139** (2009), 147–184.
- T. Matala-aho, On irrationality measures of $\sum_{l=0}^\infty d^l/\prod_{j=1}^l(1+d^jr+d^{2j}s)$, *J. Number Theory* **128** (2008), 1–16.
- G. Rhin and C. Viola, The group structure for $\zeta(3)$, *Acta Arith.* **97** (2001), 269–293.
- D. Ridout, Rational approximations to algebraic numbers, *Mathematika* **4** (1957), 125–131.
- D. Zeilberger and W. Zudilin, The irrationality measure of $\pi$ is at most $7.103205334137\ldots$, *Moscow J. Combin. Number Theory* **9** (2020), 407–419.
- Repository: [`arithmetic-hankel-determinants.md`](arithmetic-hankel-determinants.md) (Phase 26 Track B); [`classical-constants-frontier.md`](../phase25/classical-constants-frontier.md) (`GF-47`); [`partitions-and-reciprocals.md`](../phase25/partitions-and-reciprocals.md) (`GF-45`); [`nonlinear-and-badly-approx.md`](../phase25/nonlinear-and-badly-approx.md) (`GF-46`); [`binary-partition-and-carry-complexity.md`](../phase23/binary-partition-and-carry-complexity.md) (`GF-32`).
