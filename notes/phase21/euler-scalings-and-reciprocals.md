# Rational multiples of Euler's powers, and a normal reciprocal of a kernel element

Phase 21, Track D, sub-tracks D1 and D2. Fix a radix $b\ge2$. For real $z$ write $x_n=\{b^nz\}$, $D_N(z)=D_N(z;b)$ for the extreme interval discrepancy of $x_0,\dots,x_{N-1}$, $\|\cdot\|$ for the distance to the nearest integer and $e(t)=e^{2\pi it}$. As in Phases 19–20, $K_b=\{z:D_N(z)\to1\}$, and $E_b=\prod_{k\ge1}(1-b^{-k})$. For a positive integer $d$ coprime to $b$ let $t=\operatorname{ord}_d(b)$.

**Theorem D1 (rational multiples).** Let $d\ge2$ be coprime to $b$ and $\gcd(a,d)=1$.

1. $D_N\bigl(\tfrac ad E_b\bigr)$ converges to a rational number $D_\infty\in[1/d,1)$, computed by a finite automaton on pairs $(k\bmod L,\ u\in\mathbb Z/d)$ with $L=\operatorname{lcm}(2,t)$. The error is $O_{b,d,a}(\log N/\sqrt N)$ at every prefix. The limit law is an explicit rational atomic measure on $\tfrac1d\mathbb Z/\mathbb Z$. $D_N$ does **not** oscillate: the inter-insertion runs of lengths $k$ and $2k+1$ (i.e. $2j,4j+1,2j+1,4j+3$ for $k=2j,2j+1$) grow linearly with one common slope per run type, so every residue class of the automaton carries a convergent share.
2. The same holds for $\tfrac adE_b^3$, with an automaton of period at most $\operatorname{lcm}(t,2d)\cdot d$. In particular $\tfrac adE_b^3\notin K_b$. This proves the statement sketched in Phase 20, Theorem 8.
3. For odd $b$ and odd $a$, $D_N\bigl(\tfrac a2E_b^2\bigr)\to\tfrac23$, unconditionally. More generally, $\tfrac adE_b^2\in K_b$ if and only if $a/d\in\mathbb Z[1/b]$. The case of a denominator with an odd prime factor coprime to $b$ uses the Phase 20 eigenform input, Wirsing's theorem and a standard uniform upper-bound sieve.

**Theorem D2 (normal reciprocals).** There are explicit irrational $x\in K_b$ whose reciprocal $1/x$ is normal in base $b$; that is, $D_N(1/x)\to0$ along **all** $N$. For example, take

```math
x=\prod_{k\ge1}\bigl(1-b^{-m_k}\bigr),
```

where $m_1<m_2<\cdots$, the order $T_k$ of $b$ modulo the denominator $D_k$ of $\prod_{j\le k}b^{m_j}/(b^{m_j}-1)$ divides $m_{k+1}$, and $m_{k+1}/T_k\to\infty$. A canonical choice is $m_{k+1}=(k+1)m_kT_k$. Then $1-D_N(x)\le N^{-1+o(1)}$, so $x$ lies deep in $K_b$, and $1/x=\prod_kb^{m_k}/(b^{m_k}-1)$ is normal. If the sign is flipped, $x'=\prod(1+b^{-m_k})$ still lies in $K_b$ but $\limsup D_N(1/x')\ge\tfrac12$.

| Result | Status |
| --- | --- |
| Lemma 1.1 (atomic limit lemma), Lemma 1.2 (runs) | Paper proofs; finite inequality checked at every reported cutoff |
| Theorem D1.1, Corollary D1.2, Proposition D1.0 ($E_b$) | Paper proofs; automata and laws exact (script) |
| Theorem D1.3 ($E_b^3$) | Paper proof; automata exact (script) |
| Theorem D1.4 ($E_b^2/2$, $b$ odd) | Paper proof; unconditional rate $O(\log\log N/\sqrt{\log N})$ |
| Theorem D1.5 ($E_b^2/d$, non-membership) | $d$ with a factor 2 coprime to $b$: paper proof. Odd prime factor: paper proof from cited inputs; the sieve step (Lemma S) is sketched |
| Exact limit law of $E_b^2/d$ for odd $d>1$ | **Open**; finite residue laws look uniform |
| Theorem D2, Lemmas D2.1–D2.4, Propositions D2.3 and D2.5 | Paper proofs; band identity, Fourier vanishing and window bound checked exactly or with certified error (script) |

All finite statements come from [`scripts/phase21_euler_reciprocals.py`](../../scripts/phase21_euler_reciprocals.py) (§7). The algebraic and harmonic finite cores (band identity Lemma D2.1, alternating-sign band identity Proposition D2.5, character-sum vanishing Lemma D2.2, and pure periodicity of the Euler automaton) are kernel-verified in [`NormalityChecker/NormalReciprocalCore.lean`](../../NormalityChecker/NormalReciprocalCore.lean); §6 lists both those verified declarations and remaining Lean targets.

## 1. Two finite lemmas

For a probability vector $w$ on $\mathbb Z/d$, identified with $\sum_jw_j\delta_{j/d}$, define the **atomic discrepancy**

```math
D^*(w)=\max\Bigl(\max_{\text{closed atom arcs }A}\bigl(w(A)-|A|\bigr),\ \max_{\text{open atom arcs }A}\bigl(|A|-w(A)\bigr)\Bigr).
```

A closed atom arc consists of the atoms $i/d,\dots,(i+\ell)/d$ ($0\le\ell<d$) and has length $\ell/d$. An open atom arc is $(i/d,(i+\ell)/d)$ ($1\le\ell\le d$), of length $\ell/d$. This is a finite maximum of rationals. Every atomic law has $D^*\ge1/d$, since an open arc between adjacent atoms contains no atom. $D^*(w)=1$ iff $w$ is a Dirac mass.

**Lemma 1.1 (atomic limit lemma).** Let $N\ge1$, $x_0,\dots,x_{N-1}\in\mathbb R/\mathbb Z$, let $G\subseteq[0,N)$, and let $\alpha_n\in\mathbb Z/d$ satisfy $\|x_n-\alpha_n/d\|\le\eta<1/(4d)$ for $n\in G$. Put $\mu^G(j)=\#\{n\in G:\alpha_n=j\}/N$ and $\beta=1-|G|/N$. For every probability vector $w$,

```math
\bigl|D_N-D^*(w)\bigr|\le\|\mu^G-w\|_1+\beta+2\eta .
```

*Proof.* The interval discrepancy of a finite set equals its arc discrepancy (Phase 20, §0), so we may work with arcs $J$.

*Upper bound for mass minus length.* If $|J|+2\eta\ge1$, then $\#J/N-|J|\le1-|J|\le2\eta$. If no atom lies within $\eta$ of $J$, then $J$ contains no good sample, so $\#J/N-|J|\le\beta$. Otherwise the atoms within $\eta$ of $J$ form a nonempty closed atom arc $A$ with $|A|\le|J|+2\eta$, so

```math
\#J/N-|J|\le\mu^G(A)+\beta-|A|+2\eta\le D^*(w)+\|\mu^G-w\|_1+\beta+2\eta .
```

*Upper bound for length minus mass.* If $|J|\le2\eta$, then $|J|-\#J/N\le2\eta$. If all $d$ atoms lie at distance $>\eta$ inside $J$, then $J$ contains every good sample, so $|J|-\#J/N\le1-(1-\beta)=\beta$. Otherwise the atoms at distance $>\eta$ inside $J$ are the atoms of an open atom arc $A$ (possibly empty of atoms, of length $1/d$) with $|A|\ge|J|-2\eta$, giving $|J|-\#J/N\le|A|-\mu^G(A)+2\eta\le D^*(w)+\|\mu^G-w\|_1+2\eta$.

*Lower bounds.* For a closed atom arc $A$, take $J=A$ enlarged by $\eta'\downarrow\eta$ on both sides. For an open atom arc, take $J$ shrunk by $\eta'$ on both sides. Then $J$ contains, respectively misses, all good samples of the relevant atoms. $\square$

**Lemma 1.2 (runs).** Let $u\in\mathbb Z/d$ and let $O(u)=\{ub^i\}$ be its orbit under multiplication by $b$, of size at most $t$. Let $\nu(u)$ be the uniform probability on $O(u)$. Over $g$ consecutive steps $u,ub,\dots,ub^{g-1}$, each point of $O(u)$ is visited $\lfloor g/|O|\rfloor$ or $\lceil g/|O|\rceil$ times. Hence the visit-count vector differs from $g\,\nu(u)$ by at most $t$ in $\ell^1$. $\square$

## 2. D1 for Euler's product

### 2.1 The automaton

Let $0=p_0<p_1<\cdots$ be the generalized pentagonal numbers, with signs $s_0=1$ and $s=(-1)^k$ at $P_k^\pm=k(3k\pm1)/2$, so that $E_b=\sum_js_jb^{-p_j}$. Define the integral head and the tail by

```math
I_n=\sum_{p_j\le n}s_j\,b^{\,n-p_j}\in\mathbb Z,\qquad \tau_n=b^nE_b-I_n,\qquad |\tau_n|\le\frac{b^{1-r_n}}{b-1},
```

where $r_n\ge1$ is the distance from $n$ to the next insertion. Then $x_n=\{aI_n/d+a\tau_n/d\}$. Inside a run, $I_{n+1}=bI_n$; at an insertion, $I_p=bI_{p-1}+s_p$. Write $u_k^\pm=I_{P_k^\pm}\bmod d$ and $u_0^+=1$. Then

```math
u_k^-=b^{2k-1}u_{k-1}^++(-1)^k,\qquad u_k^+=b^ku_k^-+(-1)^k .
```

The run after $P_k^-$ has length $k$ and visits $u_k^-b^i$; the run after $P_k^+$ has length $2k+1$ and visits $u_k^+b^i$. The step $(k-1\bmod L,u_{k-1}^+)\mapsto(k\bmod L,u_k^+)$ depends on $k$ only modulo $L=\operatorname{lcm}(2,t)$ and is bijective in $u$. A bijection of a finite set has purely periodic orbits, so $k\mapsto(k\bmod L,u_k^+)$ is purely periodic with some period $P$, where $L\mid P\le Ld$. Define

```math
\mu_{b,a/d}=\frac1P\sum_{k=1}^{P}\Bigl(\tfrac13\,a_*\nu(u_k^-)+\tfrac23\,a_*\nu(u_k^+)\Bigr),
```

where $a_*$ is multiplication by $a$. This is a rational probability on $\tfrac1d\mathbb Z/\mathbb Z$, invariant under multiplication by $b$.

**Theorem D1.1.** For $d\ge2$ coprime to $b$ and $\gcd(a,d)=1$,

```math
\Bigl|D_N\bigl(\tfrac adE_b;b\bigr)-D^*(\mu_{b,a/d})\Bigr|\le C_{b,d,a}\,\frac{\log N}{\sqrt N}\qquad(N\ge2),
```

and $D_\infty=D^*(\mu_{b,a/d})\in\mathbb Q\cap[1/d,1)$.

*Proof.* Put $R=\lceil\log_b(4|a|N)\rceil+1$ and $G=\{n<N:r_n\ge R\}$. For $n\in G$, $\|x_n-\alpha_n/d\|\le\eta:=1/(4dN)<1/(4d)$ with $\alpha_n=aI_n\bmod d$ (valid for all $N\ge2$). The complement satisfies $|[0,N)\setminus G|\le R\,(\sqrt{24(N+R)+1}/3+1)=O(\sqrt N\log N)$ (Phase 20, §1). By Lemma 1.1 it remains to bound $\|\mu^{\rm all}-\mu\|_1$, where $\mu^{\rm all}$ counts $\alpha_n$ over all $n<N$; removing $[0,N)\setminus G$ costs its proportion again.

Let the prefix contain the complete runs of the pairs $k\le K$ plus any leftover (at most $n=0$, the minus-run of pair $K+1$ of length $K+1$, and a partial plus-run of length $<2K+3$, totalling $\le3K+4$). Then $N=\tfrac32K^2+O(K)$, so $K\asymp\sqrt N$. Lemma 1.2 costs at most $t$ per run, $O(t\sqrt N)$ in total, and the leftover costs at most $(3K+4)/N$. For a class $c\bmod P$,

```math
\sum_{k\le K,\ k\equiv c}k=\frac{K^2}{2P}+O(K+P),\qquad \sum_{k\le K,\ k\equiv c}(2k+1)=\frac{K^2}{P}+O(K+P),
```

so each of the $2P$ run classes receives weight $\tfrac1{3P}$ or $\tfrac2{3P}$ up to $O(P/K)$. Summing gives $\|\mu^{\rm all}-\mu\|_1=O_{b,d}(P^2/\sqrt N)$. $D^*<1$ because $\mu$ is not a Dirac mass. A Dirac mass would force $u_k^-=u_k^+=v$ with $bv=v$ throughout the cycle, but then $u_k^+=b^kv+(-1)^k=v\pm1\ne v$. $\square$

**Why there is no oscillation.** The brief asked whether the unequal run lengths ($2j,4j,2j+1,4j+2$ for constant-digit runs, or $k$ and $2k+1$, i.e. $2j,4j+1,2j+1,4j+3$, for the automaton's inter-insertion runs) could make the empirical law depend on where $N$ falls. They cannot. The share of a class $k\equiv c\pmod P$ among minus-runs is $\sum_{k\equiv c}k/\sum_k(3k+1)\to1/(3P)$, uniformly in $c$, because the length is the **same** linear function of $k$ for every class. A prefix ending inside block $j$ moves weights by $O(j/j^2)=O(1/\sqrt N)$. Oscillation would require lengths that grow geometrically or depend on the class.

**Proposition D1.0 (general denominators, any $z\in K_b$).** Let $z\in K_b$ (in particular $z=E_b,E_b^3,E_b^2$), and let $a/d$ be reduced with $d=d_0d_1$, where every prime of $d_0$ divides $b$ and $\gcd(d_1,b)=1$. Choose $e$ with $d_0\mid b^e$ and write $ab^e/d_0=a'+jd_1$ with $0\le a'<d_1$. Then

```math
\Bigl|D_N\bigl(\tfrac adz\bigr)-D_N\bigl(\tfrac{a'}{d_1}z\bigr)\Bigr|\le\frac{2e}N+|j|\bigl(1-D_N(z)\bigr)
```

(which is $O(\log N/\sqrt N)$ for $z=E_b$ or $E_b^3$, and $o(1)$ for every $z\in K_b$).

*Proof.* The orbit of $b^e(\tfrac adz)$ is the orbit of $\tfrac adz$ shifted by $e$, changing $D_N$ by at most $2e/N$. The term $jz$ is a translation by a $K_b$ element, controlled by the Phase 20 additive bound. $\square$

So $D_\infty(\tfrac adE_b)=D_\infty(\tfrac{a'}{d_1}E_b)$, which equals 1 iff $d_1=1$. This recovers Phase 20, Theorem 8(b).

### 2.2 Closed forms and tables

**Corollary D1.2.** Let $d=p$ be prime with $b$ a primitive root mod $p$. Every $\times b$-invariant law has the form $w_0\delta_0+u\sum_{j\ne0}\delta_{j/p}$ with $u=(1-w_0)/(p-1)$, and

```math
D^*=\max\Bigl(w_0,\ u,\ \frac2p-w_0,\ \frac{p-1}p-(p-2)u\Bigr)=\max\Bigl(w_0,\ \frac2p-w_0\Bigr)=\frac1p+\Bigl|w_0-\frac1p\Bigr|.
```

*Proof.* Closed arcs of $k$ consecutive units give $ku-(k-1)/p$; closed arcs through 0 give $w_0+ku-k/p$; open arcs give $\ell/p$ minus the enclosed mass. Each family is linear in its length, so its extremes occur at the end points, giving the four-term maximum. Since $\frac{p-1}p-(p-2)u=w_0+u-\frac1p\le\max(w_0,u)$ always and $u\le\frac2p-w_0$ whenever $w_0<\frac1p$, the maximum simplifies to $\max(w_0,\frac2p-w_0)=\frac1p+|w_0-\frac1p|$. $\square$

The script confirms the formula for both $E_b$ and $E_b^3$ in 12 cases, and also computes $w_0$ there: for instance $w_0(E_2)=1/6,1/12,1/10,1/12,1/54$ for $p=3,5,11,13,19$.

Exact limits of $D_N(\tfrac adE_b;b)$ for $a=1$. Here "units" means each residue coprime to $d$, $P$ is the automaton period, and the law is given only when it is short.

| $b$ | $d$ | $P$ | law $\mu_{b,1/d}$ | $D_\infty$ |
|---|---|---|---|---|
| 2 | 3 | 2 | $\tfrac16$ at 0, $\tfrac5{12}$ at each unit | $\tfrac12$ |
| 2 | 5 | 4 | $\tfrac1{12}$ at 0, $\tfrac{11}{48}$ at each unit | $\tfrac{19}{60}$ |
| 2 | 7 | 6 | $\tfrac19$ at 0, $\tfrac4{27}$ at each unit | $\tfrac{11}{63}$ |
| 2 | 9 | 6 | $\tfrac16$ at 0, $\tfrac5{36}$ at each unit, 0 at $3,6$ | $\tfrac5{18}$ |
| 2 | 15 | 4 | 13 atoms | $\tfrac7{30}$ |
| 2 | 11 | 10 | $\tfrac1{10}$ at 0, $\tfrac9{100}$ at each unit | $\tfrac1{10}$ |
| 3 | 2 | 2 | $\tfrac13,\tfrac23$ | $\tfrac23$ |
| 3 | 4 | 2 | $\tfrac16,\tfrac13,\tfrac16,\tfrac13$ | $\tfrac13$ |
| 3 | 5 | 4 | $\tfrac5{12}$ at 0, $\tfrac7{48}$ at each unit | $\tfrac5{12}$ |
| 3 | 7 | 6 | $\tfrac5{18}$ at 0, $\tfrac{13}{108}$ at each unit | $\tfrac5{18}$ |
| 3 | 8 | 2 | $\tfrac16,\tfrac16,\tfrac1{12},\tfrac16,0,\tfrac16,\tfrac1{12},\tfrac16$ | $\tfrac14$ |
| 10 | 3 | 2 | uniform | $\tfrac13$ |
| 10 | 7 | 6 | as for $b=3$ | $\tfrac5{18}$ |

The rows $(2,3)$ and $(3,2)$ are Phase 20's values. For every odd $b$, $\mu_{b,1/2}=(\tfrac13,\tfrac23)$ and $D_\infty=\tfrac23$: $I_n$ is odd exactly on the runs after $P_k^+$. For $b=10,d=3$ every residue is fixed ($10\equiv1$) and the law is exactly uniform, and the script finds $|D_N-\tfrac13|<10^{-6}$ at $2^{12},2^{14},2^{16}$.

**The numerator matters.** $D_\infty(\tfrac adE_b)$ depends only on the class of $a$ in $(\mathbb Z/d)^\times/\langle b,-1\rangle$. It is constant when $\langle b,-1\rangle$ is the whole unit group; for example $D_\infty(\tfrac a7E_2)=\tfrac{11}{63}$ for all six $a$. Otherwise it varies. The script finds 2 values for $(b,d)=(2,17)$ ($\tfrac{133}{1632},\tfrac7{68}$), 3 for $(2,31)$, 3 for $(5,13)$ and 5 for $(10,11)$ (from $\tfrac{25}{66}$ to $\tfrac{43}{66}$).

**Certified convergence.** The script checks the inequality of Lemma 1.1, $|D_N-D_\infty|\le\|\mu^G-\mu\|_1+\beta+2\eta$, at $N=2^{12},2^{14},2^{16}$ in nine cases. The observed $|D_N-D_\infty|\sqrt N/\log_bN$ stays between $0.000$ (`1E_10/3`, exact uniform law) and $0.451$ (`1E_3/2` at $N=4096$). For example, $D_N(\tfrac13E_2;2)=0.4414,0.4663,0.4819$, and $D_N(\tfrac17E_2;2)=0.1479,0.1620,0.1666$ against $\tfrac{11}{63}=0.1746$. With the cautious choice of $R$, the bound is dominated by $\beta$, the share of shifts within $R$ of an insertion. It is valid but not sharp, and a matching lower bound of order $\log N/\sqrt N$ is not claimed.

## 3. D1 for Jacobi's cube

Here $E_b^3=\sum_{k\ge0}(-1)^k(2k+1)b^{-T_k}$ with $T_k=k(k+1)/2$; the gap before $T_k$ is $k$ and the run after $T_k$ has length $k+1$. With $v_k=I_{T_k}\bmod d$,

```math
v_0=1,\qquad v_k=b^k\,v_{k-1}+(-1)^k(2k+1)\pmod d .
```

The coefficients $(-1)^k(2k+1)\bmod d$ have period dividing $2d$, and $b^k\bmod d$ has period $t$. The step depends only on $k$ modulo $L_3=\operatorname{lcm}(t,2d)$ and is bijective in $v$, so $(k\bmod L_3,v_k)$ is purely periodic with some period $P_3$. All runs have the same slope, so all classes carry equal weight.

**Theorem D1.3.** For $d\ge2$ coprime to $b$ and $\gcd(a,d)=1$, put $\mu^{(3)}=\frac1{P_3}\sum_{k=1}^{P_3}a_*\nu(v_k)$. Then $|D_N(\tfrac adE_b^3)-D^*(\mu^{(3)})|=O_{b,d,a}(\log N/\sqrt N)$, and $D^*(\mu^{(3)})\in\mathbb Q\cap[1/d,1)$. In particular $\tfrac adE_b^3\notin K_b$.

*Proof.* The proof of Theorem D1.1 applies with $R=\lceil\log_b(4|a|(2K+3)N)\rceil$, since the coefficient size $2k+1=O(\sqrt N)$ only enlarges $R$ by a constant factor. There are $\sqrt{2N}+O(1)$ insertions. For $D^*<1$: a Dirac law forces every $v_k$ in the cycle to be one fixed point $v=bv$. Then $v=v+(-1)^k(2k+1)$, so $d\mid2k+1$ for all $k$. Two consecutive $k$ would give $d\mid2$, and $2k+1$ is odd. $\square$

| $b$ | $d$ | $P_3$ | law $\mu^{(3)}_{b,1/d}$ | $D_\infty(E^3)$ | $D_\infty(E)$ |
|---|---|---|---|---|---|
| 2 | 3 | 6 | $\tfrac16,\tfrac5{12},\tfrac5{12}$ | $\tfrac12$ | $\tfrac12$ |
| 2 | 5 | 20 | $\tfrac3{20}$ at 0, $\tfrac{17}{80}$ at each unit | $\tfrac14$ | $\tfrac{19}{60}$ |
| 2 | 7 | 42 | uniform | $\tfrac17$ | $\tfrac{11}{63}$ |
| 2 | 9 | 18 | $\tfrac1{18}$ at $0,3,6$, $\tfrac5{36}$ at each unit | $\tfrac16$ | $\tfrac5{18}$ |
| 2 | 15 | 60 | — | $\tfrac7{60}$ | $\tfrac7{30}$ |
| 2 | 11 | 110 | — | $\tfrac1{10}$ | $\tfrac1{10}$ |
| 3 | 2 | 4 | $\tfrac12,\tfrac12$ | $\tfrac12$ | $\tfrac23$ |
| 3 | 4 | 8 | $\tfrac12$ at 0, $\tfrac14$ at $1,3$ | $\tfrac12$ | $\tfrac13$ |
| 3 | 5 | 20 | $\tfrac25$ at 0, $\tfrac3{20}$ at each unit | $\tfrac25$ | $\tfrac5{12}$ |
| 3 | 7 | 42 | $\tfrac5{42}$ at 0, $\tfrac{37}{252}$ at each unit | $\tfrac16$ | $\tfrac5{18}$ |
| 3 | 8 | 16 | $\tfrac12$ at 0, $\tfrac18$ at each unit | $\tfrac12$ | $\tfrac14$ |
| 10 | 3 | 6 | uniform | $\tfrac13$ | $\tfrac13$ |
| 10 | 7 | 42 | as for $b=3$ | $\tfrac16$ | $\tfrac5{18}$ |

**Comparison.** There is no general inequality between $D_\infty(E^3)$ and $D_\infty(E)$. Usually $D_\infty(E^3)\le D_\infty(E)$, because the odd coefficients $2k+1$ move the residue more often: for $b$ odd, $d=2$, every insertion flips the parity and the law is $(\tfrac12,\tfrac12)$. But $(b,d)=(3,4)$ and $(3,8)$ reverse the order ($\tfrac12>\tfrac13$, $\tfrac12>\tfrac14$): by induction, for $b=3$ and $d\in\{4,8\}$ one has $v_{2m}\equiv4m+1\pmod d$ and $v_{2m+1}\equiv3(4m+1)-(4m+3)=8m\equiv0\pmod d$, so $v_k=0$ on every odd $k$ (mass $\tfrac12$ at $0$). In several cases ($(2,7)$, $(2,31)$, $(2,73)$, $(3,13)$, $(2,23)$, all verified by the script) the cube law is exactly uniform and $D_\infty(E^3)=1/d$, the least possible value. The finite values $D_N(\tfrac13E_2^3;2)=0.360,0.421,0.456$ at $2^{12},2^{14},2^{16}$ approach $\tfrac12$ at the predicted rate, with ratio $|D_N-D_\infty|\sqrt N/\log_2N\approx0.72$.

## 4. D1 for Euler's square

Write $E(q)=\prod_{n\ge1}(1-q^n)$ and $E(q)^2=\sum a_2(n)q^n$. The Phase 20 coefficient-transfer facts used below are elementary. The support of $a_2$ has counting function $\ll X/\sqrt{\log X}$ (Landau), and $\sum_{n\le X}|a_2(n)|=O(X)$ (pair count). These give $1-D_N(E_b^2)=O(\log\log N/\sqrt{\log N})$. Phase 20, Theorem 6, improves the rate to $O(\log\log N/(\log N)^{3/4})$ using the cited eigenform input.

### 4.1 Denominator 2

**Theorem D1.4.** Let $b$ and $a$ be odd. Then

```math
\Bigl|D_N\bigl(\tfrac a2E_b^2;b\bigr)-\tfrac23\Bigr|=O_{a,b}\Bigl(\frac{\log\log N}{\sqrt{\log N}}\Bigr),
```

with $O(\log\log N/(\log N)^{3/4})$ granting the Phase 20 eigenform input. In particular $\tfrac a2E_b^2\notin K_b$.

*Proof.* In $\mathbb Z[[q]]$, $(1-q^n)^2=1-q^{2n}-2q^n(1-q^n)$, so $E(q)^2=E(q^2)+2G(q)$ with $G\in\mathbb Z[[q]]$; this is Frobenius modulo 2. The coefficients $g_n=(a_2(n)-[n=2p]s_p)/2$ are supported in $\operatorname{supp}a_2\cup2\cdot\text{Pent}$, with $|g_n|\le(|a_2(n)|+1)/2$. The same transfer as for $E_b^2$ therefore gives $1-D_N(G(1/b))=O(\log\log N/\sqrt{\log N})$. Now

```math
\tfrac a2E_b^2=\tfrac a2E(b^{-2})+a\,G(1/b),\qquad \Bigl|D_N\bigl(\tfrac a2E_b^2\bigr)-D_N\bigl(\tfrac a2E(b^{-2})\bigr)\Bigr|\le|a|\bigl(1-D_N(G(1/b))\bigr)
```

by the additive bound of Phase 20, §4.5. The proof of Theorem D1.1 applies verbatim to $E(q^2)$ at $q=1/b$: insertion positions $2P_k^\pm$, run lengths $2k$ and $4k+2$, weights still $\tfrac13,\tfrac23$. For $d=2$ and odd $b$, $I_n\bmod2$ is the number of insertions up to $n$, so it is $0$ after $2P_k^-$ and $1$ after $2P_k^+$. The law is $\tfrac13\delta_0+\tfrac23\delta_{1/2}$ and $D^*=\tfrac23$, with error $O(\log N/\sqrt N)$. $\square$

The script checks $E(q)^2\equiv E(q^2)\pmod2$ through $q^{20000}$, the law $(\tfrac13,\tfrac23)$ for $b=3,5,7,9,11$, and $I_n(E_3^2)\equiv I_n(E(3^{-2}))\pmod2$ for every $n<2^{17}$. The residue law of the shifts with small tails is $(0.3301,0.6699)$ at $N=2^{17}$. Even so, $D_N(\tfrac12E_3^2;3)=0.127,0.146,0.163,0.170$ at $N=2^{12},2^{14},2^{16},2^{17}$ is still far from $\tfrac23$. The reason is that 75% of the shifts at $2^{17}$ have a tail $|\tau_n|/2>0.02$, the same slow kernel convergence as $1-D_{2^{20}}(E_2^2)=0.79$ in Phase 20. The theorem is asymptotic, and these values neither support nor contradict it.

### 4.2 Non-membership for every denominator

**Theorem D1.5.** For reduced $a/d$, $\tfrac adE_b^2\in K_b$ if and only if $a/d\in\mathbb Z[1/b]$.

Scope. "If" is elementary. "Only if" is unconditional when the $b$-coprime part $d_1$ of $d$ is even. When $d_1$ has an odd prime factor $\ell$, the proof below uses three inputs:

- Phase 20, Theorem 6(a), the eigenform description of $a_2$;
- Wirsing's lower bound for a multiplicative set of prime density $\tfrac14$;
- Lemma S, a standard Selberg upper-bound sieve, uniform in the shift $h$. Its proof is only sketched.

*Proof.* If $a/d=a''b^{-e}$, then $a''E_b^2\in K_b$ (integer multiple) and $D_N(b^{-e}z)$ differs from $D_N(z)$ by at most $2e/N$.

Conversely, suppose $d_1>1$. By Proposition D1.0, $\tfrac{a'}{d_1}E_b^2\in K_b$ for some $a'$ coprime to $d_1$. Multiplying by an integer inverse of $a'$ modulo $d_1$ and subtracting an integer multiple of $E_b^2\in K_b$ gives $\tfrac1{d_1}E_b^2\in K_b$. Multiplying by $d_1/\ell$ for a prime $\ell\mid d_1$ gives $\tfrac1\ell E_b^2\in K_b$. For $\ell=2$ this contradicts Theorem D1.4. Let $\ell$ be odd.

*(i) Atoms.* With $I_n=\sum_{m\le n}a_2(m)b^{n-m}$ and $\tau_n=b^nE_b^2-I_n$, the coefficient transfer gives $\#\{n<N:|\tau_n|>\varepsilon\}=o(N)$ for each fixed $\varepsilon>0$. So for density-one $n$, $x_n$ lies within $o(1)$ of $(I_n\bmod\ell)/\ell$.

By Phase 19, $K_b=F_b+\{w:M_N(w)\to0\}$. Membership therefore gives $c'$ with $(b-1)c'\in\mathbb Z$ and $\frac1N\sum\|x_n-c'\|\to0$, because $b^nc'\equiv c'$. Hence $c'=c/\ell$, $bc\equiv c\pmod\ell$, and $I_n\equiv c$ for density-one $n$.

*(ii) Runs.* Let $S_\ell=\{n:\ell\nmid a_2(n)\}=\{n_1<n_2<\cdots\}$ be the effective support and $G_i=n_{i+1}-n_i$. On $[n_i,n_{i+1})$ the residue moves by multiplication by $b$, so the run either sits at the fixed class $c$ or never meets it. Two consecutive runs cannot both sit at $c$, since $I_{n_{i+1}}\equiv c+a_2(n_{i+1})\not\equiv c$.

*(iii) Counting.* By Theorem 6(a), $a_2(n)=\pm2^{\omega}$ whenever $12n+1$ is a squarefree product of primes $\equiv1\pmod{12}$ times a square of primes $\not\equiv1\pmod{12}$. Such $n$ lie in $S_\ell$ for odd $\ell$. By Wirsing,

```math
|S_\ell\cap(N/2,N]|\ge\kappa\,N/(\log N)^{3/4}.
```

The script confirms $|S'\cap[1,2^{15}]|\,(\log X)^{3/4}/X=2.12$. By Lemma S, at most $2C_0HN/(\log N)^{3/2}$ elements of $(N/2,N]$ have another support point within distance $H$. Take $H=\lfloor\kappa(\log N)^{3/4}/(4C_0)\rfloor$. Then at least half of $S_\ell\cap(N/2,N]$ have both neighbouring gaps $\ge H$. At each such $n_i$, one of the runs ending or starting at $n_i$ avoids $c$ on a stretch of length $H$ next to $n_i$. These stretches overlap at most twice. Hence

```math
\#\{n<N+H:\ I_n\not\equiv c\}\ \ge\ \frac H4\cdot\frac{\kappa N}{(\log N)^{3/4}}\ \ge\ \frac{\kappa^2}{20\,C_0}\,N
```

for large $N$, which contradicts (i). $\square$

**Lemma S (sketch).** There is $C_0$ such that, uniformly for $1\le H\le(\log N)^2$,

```math
\sum_{1\le h\le H}\#\{n\le N:\ a_2(n)\,a_2(n+h)\ne0\}\le C_0\,\frac{HN}{(\log N)^{3/2}} .
```

*Sketch.* By Theorem 6(a), $a_2(n)\ne0$ forces $12n+1=uv^2$, where $u$ has only prime factors $\equiv1\pmod{12}$ and $v$ only primes $\ge5$, $\not\equiv1\pmod{12}$. Pairs with $v>V=(\log N)^3$ or $v'>V$ number $\ll N/V+\sqrt N$ per $h$. For fixed $v,v'\le V$, impose $v^2\mid12n+1$ and $v'^2\mid12n+12h+1$; this is at most one class modulo $\operatorname{lcm}(v^2,v'^2)$ and empty unless $\gcd(v,v')\mid h$. Sift the two cofactors by the primes $p\le N^{1/10}$, $p\ge5$, $p\not\equiv1\pmod{12}$. These primes have density $\tfrac34$, so the problem has dimension $\tfrac32$. The Selberg upper bound (Halberstam–Richert, *Sieve Methods*, Thm. 5.1) gives

```math
\ll\mathfrak S(h)\,\frac{N}{\operatorname{lcm}(v^2,v'^2)}\Bigl(\frac v{\varphi(v)}\frac{v'}{\varphi(v')}\Bigr)^{2}(\log N)^{-3/2},\qquad \mathfrak S(h)\le\prod_{p\mid h}\bigl(1+\tfrac2p\bigr).
```

The sum over $v,v'$ converges, and $\sum_{h\le H}\mathfrak S(h)\ll H$. This replaces the $(\log\log N)^{3/2}$ loss of the cruder Phase 20 version, which would not suffice here. $\square$

The script records the alternation functional $\frac1X\sum_i\min(G_i,G_{i+1})$ at $X=2^{17}$. It equals $0.6051$ for $\ell=3$ and $0.6063$ for $\ell=5,7$, while the proof needs only a positive constant.

### 4.3 What remains open for $E_b^2$

For odd $d>1$ coprime to $b$, neither the existence of $\lim D_N(\tfrac adE_b^2)$ nor the limiting residue law is proved. The residue $I_n\bmod d$ makes a walk driven by the gaps of a $\tfrac34$-dimensional multiplicative set and by the values $a_2(n)\bmod d$. Its equidistribution amounts to correlations of $a_2$ at shifts up to $(\log N)^{O(1)}$, beyond current sieve technology. Finite residue laws of the shifts with small tails are close to uniform at $N=2^{16}$:

- $(0.348,0.327,0.325)$ for $E_2^2/3$;
- $(0.199,0.199,0.202,0.197,0.202)$ for $E_2^2/5$;
- within $0.01$ of $\tfrac15$ for $E_3^2/5$;
- within $0.006$ of $\tfrac17$ for $E_2^2/7$.

This suggests, for prime $\ell\nmid 2b$, the uniform law and $D_\infty=1/\ell$. We state it only as a question. The finite discrepancies at $2^{16}$ ($0.0258$–$0.0542$) are dominated by the 63–87% of shifts whose tails are still large.

## 5. D2: a kernel element with a normal reciprocal

### 5.1 Statement

Let $m_1<m_2<\cdots$ be positive integers and put

```math
R_k=\prod_{j\le k}\frac{b^{m_j}}{b^{m_j}-1}=\prod_{j\le k}\bigl(1-b^{-m_j}\bigr)^{-1},\qquad R_0=1 .
```

Let $D_k=\prod_{j\le k}(b^{m_j}-1)$ be the reduced denominator of $R_k$ (already in lowest terms since $\gcd(b^{\sum m_j},\prod(b^{m_j}-1))=1$). Let $T_k=\operatorname{ord}_{D_k}(b)$, with $D_0=T_0=1$. Call $(m_k)$ **admissible** if

```math
\text{(A1)}\quad T_k\mid m_{k+1}\quad(k\ge1),\qquad\qquad \text{(A2)}\quad \omega_k=m_{k+1}/T_k\to\infty .
```

For example $m_{k+1}=(k+1)m_kT_k$. For $b=2$ one admissible start is $m=(2,4,48,43200,\ldots)$, with $(D_k)=(3,\,45,\,12666373951979475,\ldots)$ and $(T_k)=(2,12,2160,\ldots)$.

**Theorem D2.** Let $(m_k)$ be admissible, $x=\prod_k(1-b^{-m_k})$ and $y=1/x=\lim R_k$.

(a) $1-D_N(x;b)\le N^{-1+o(1)}$. In particular $x\in K_b$.

(b) $y$ is normal in base $b$. Quantitatively, let $K\ge3$, $m_K\le N\le m_{K+1}$ and $h\ge1$, and put $W_h(N)=\frac1N\sum_{n<N}e(hb^ny)$ and $H=\min(\lfloor\sqrt{D_{K-2}}\rfloor,\,\omega_{K-1})\ge1$. Then

```math
|W_h(N)|\le\frac{3\gcd(h,D_{K-2})}{D_{K-2}}+\frac{T_{K-1}+3c_b(h)}{m_K},\qquad c_b(h)=2\log_b(64\pi h)+8,
```

```math
D_N(y)\le\frac6{H+1}+\frac{12}{\pi\sqrt{D_{K-2}}}+\frac4\pi\,\frac{\bigl(T_{K-1}+3c_b(H)\bigr)(1+\log H)}{m_K},
```

and both right sides tend to 0 as $K\to\infty$ under (A1) and (A2) alone.

(c) $x$ and $y$ are irrational.

Since $D_N(y)\to0$ along every $N$, this answers the Phase 21 question affirmatively: reciprocation can carry the extreme kernel $K_b$ onto the normal numbers.

### 5.2 The band identity

**Lemma D2.1.** Let $K\ge1$ with $T_{K-1}\mid m_K$, write $m=m_K$ and $n=im+r$ with $0\le r<m$. Then

```math
b^nR_K\equiv(i+1)\,b^rR_{K-1}+\eta_r\pmod 1,\qquad \eta_r=\frac{b^rR_{K-1}}{b^m-1}\in\bigl(0,\,8b^{r-m}\bigr].
```

*Proof.* $b^nR_K=\sum_{j\ge0}b^{n-jm}R_{K-1}$. For $j\le i$, the exponent $r+(i-j)m$ is a nonnegative integer. Also $R_{K-1}=A/D_{K-1}$ and $b^m\equiv1\pmod{D_{K-1}}$, so $b^{n-jm}R_{K-1}\equiv b^rR_{K-1}\pmod1$. The terms $j>i$ sum to $\eta_r$, and $R_{K-1}<4$ because $m_j\ge j$. $\square$

So the orbit of $R_K$ consists of **bands** of length $m_K$. Band $i$ repeats the orbit of $R_{K-1}$ multiplied by $i+1$, with a correction that is negligible except within $O(\log)$ of the band end. On the zero run of $x$ after $m_K$, $1/x$ is locked to $R_K$ (the "lock" in the brief), and Lemma D2.1 says what $R_K$ looks like.

### 5.3 Exact vanishing of cycle Fourier coefficients

**Lemma D2.2.** Let $K\ge2$ with $T_{K-1}\mid m_K$, and let $\widehat C_K(k)=\frac1{T_K}\sum_{t<T_K}e(kb^tR_K)$ be the Fourier coefficients of the cycle measure of $R_K$. Then

```math
\widehat C_K(k)=0\qquad\text{unless}\quad D_{K-1}\mid k .
```

*Proof.* By Lemma D2.1, $b^tR_K\bmod1$ depends only on $(i\bmod D_{K-1},\,r)$. So $P=m_KD_{K-1}$ is a multiple of $T_K$, and the cycle average may be taken over $P$:

```math
\widehat C_K(k)=\frac1{m_KD_{K-1}}\sum_{r<m_K}e(k\eta_r)\sum_{c\in\mathbb Z/D_{K-1}}e\Bigl(\frac{c\,k\,b^rA}{D_{K-1}}\Bigr).
```

Here $c=i+1$ runs over a complete residue system, and $b^rA$ is a unit modulo $D_{K-1}$. The inner sum is $D_{K-1}\mathbf 1[D_{K-1}\mid k]$. $\square$

### 5.4 The window estimate and the proof of (b)

**Proposition D2.3.** Under (A1), with $K\ge3$, $m_K\le N\le m_{K+1}$ and $h\ge1$, the bound of Theorem D2(b) for $|W_h(N)|$ holds.

*Proof.* (1) *From $y$ to $R_K$.* We have $y-R_K=R_K\bigl(\prod_{k>K}(1-b^{-m_k})^{-1}-1\bigr)\le32\,b^{-m_{K+1}}$ (using $(1-u)^{-1}\le1+2u$ and $R_K<4$), so

```math
\sum_{n<N}\bigl|e(hb^ny)-e(hb^nR_K)\bigr|\le\sum_{l\ge1}\min(2,64\pi hb^{-l})\le c_b(h).
```

(2) *Bands.* Write $N=Im_K+r_0$ with $I\ge1$ and $0\le r_0<m_K$. In a complete band $i$, Lemma D2.1 and $|e(h\eta_r)-1|\le\min(2,16\pi hb^{r-m_K})$ give

```math
\sum_{r<m_K}e(hb^{im_K+r}R_K)=\sum_{r<m_K}e\bigl(h(i+1)b^rR_{K-1}\bigr)+O^*(c_b(h))=m_K\,\widehat C_{K-1}\bigl(h(i+1)\bigr)+O^*(c_b(h)).
```

The last step uses $T_{K-1}\mid m_K$, and $O^*(c)$ denotes a quantity of modulus at most $c$. The partial band gives $\lfloor r_0/T_{K-1}\rfloor T_{K-1}\widehat C_{K-1}(h(I+1))+O^*(T_{K-1}+c_b(h))$.

(3) *Vanishing.* By Lemma D2.2 for $K-1\ge2$, using (A1) at $K-2$, only the $a\le I$ with $D_{K-2}\mid ha$ contribute. That is, $a$ is a multiple of $D_{K-2}/g$ with $g=\gcd(h,D_{K-2})$, and there are at most $Ig/D_{K-2}$ such $a$. The partial band contributes only if $D_{K-2}/g\le I+1$, and then $r_0/N\le1/I\le2g/D_{K-2}$; if $D_{K-2}\mid h$ the bound is trivial anyway. Since $|\widehat C|\le1$ and $N\ge Im_K$,

```math
|W_h(N)|\le\frac g{D_{K-2}}+\frac{2g}{D_{K-2}}+\frac{T_{K-1}+(I+2)c_b(h)}{Im_K}\le\frac{3g}{D_{K-2}}+\frac{T_{K-1}+3c_b(h)}{m_K}.\qquad\square
```

*Proof of (b).* Apply the Erdős–Turán inequality $D_N\le\frac6{H+1}+\frac4\pi\sum_{h\le H}\frac{|W_h(N)|}h$ with $H=\min(\lfloor\sqrt{D_{K-2}}\rfloor,\omega_{K-1})\ge1$. Using $\gcd(h,D_{K-2})/h\le1$, $H\le\sqrt{D_{K-2}}$, and $\sum_{h\le H}1/h\le1+\log H$ gives the stated bound on $D_N(y)$. Under (A1)–(A2) alone, every term tends to $0$: $D_{K-2}\to\infty$ (Lemma D2.4) and $\omega_{K-1}\to\infty$ (A2) imply $H\to\infty$, so $\frac6{H+1}\to0$ and $\frac{12}{\pi\sqrt{D_{K-2}}}\to0$; next $\frac{T_{K-1}(1+\log H)}{m_K}=\frac{1+\log H}{\omega_{K-1}}\le\frac{1+\log\omega_{K-1}}{\omega_{K-1}}\to0$; finally $H\le\omega_{K-1}=m_K/T_{K-1}\le m_K$, so $\frac{3c_b(H)(1+\log H)}{m_K}\ll_b\frac{(1+\log m_K)^2}{m_K}\to0$. $\square$

**Lemma D2.4 (growth).** For an admissible sequence and every $k\ge1$, $D_k=\prod_{j\le k}(b^{m_j}-1)\ge b^{m_k}-1$ and $T_k\ge m_k$. Hence $D_k\to\infty$ and $m_{k+1}/m_k=\omega_k T_k/m_k\ge\omega_k\to\infty$.

*Proof.* Since $\gcd(b^{\sum_{j\le k}m_j},\prod_{j\le k}(b^{m_j}-1))=1$, $R_k$ is already in lowest terms, so $D_k=\prod_{j\le k}(b^{m_j}-1)\ge b^{m_k}-1$. Then $b^{T_k}-1\ge D_k\ge b^{m_k}-1$ forces $T_k\ge m_k$, and $m_{k+1}=\omega_kT_k\ge\omega_km_k$. $\square$

*Proof of (a).* Expand $x=\sum_nc(n)b^{-n}$ with $c(n)=\sum(-1)^{|S|}$ over finite $S$ with $\sum_{j\in S}m_j=n$. Let $J(X)=\#\{k:m_k\le X\}$. The support meets $[0,X]$ in at most $2^{J(X)}$ points and $|c(n)|\le2^{J(n)}$. By Lemma D2.4, $J(X)=o(\log X)$. If no support point lies in $(n,n+w]$, then $\|b^nx\|\le\sum_{l>w}2^{J(n+l)}b^{-l}\le1/N$ for $w=\lceil2\log_bN\rceil+C$. Lemma 0(a) of Phase 20 (`discrepancy_deficit_le`) then gives

```math
1-D_N(x)\le\frac2N+\frac{(w+1)\,2^{J(N+w)}}N=N^{-1+o(1)}.
```

(c) follows from (b), since normal numbers are irrational. $\square$

### 5.5 The sign of the factors decides: a dichotomy

**Proposition D2.5.** Let $\epsilon_k\in\{\pm1\}$, $x_\epsilon=\prod_k(1+\epsilon_kb^{-m_k})$ and $R_k^\epsilon=\prod_{j\le k}(1+\epsilon_jb^{-m_j})^{-1}$, with $D_k^\epsilon=\prod_{j\le k}(b^{m_j}+\epsilon_j)$ and $T_k^\epsilon=\operatorname{ord}_{D_k^\epsilon}(b)$. Assume (A1) and (A2) for these. Then $x_\epsilon\in K_b$ and:

1. if $\epsilon_K=+1$, $m_{K+1}\ge8$, and $2Jm_K\le m_{K+1}-6$, then for every integer $L\ge1$,

```math
D_{2Jm_K}(1/x_\epsilon)\ \ge\ \tfrac12\bigl(1-L/m_K\bigr)-3b^{-L};
```

2. consequently $1/x_\epsilon$ is normal **if and only if** $\epsilon_k=-1$ for all large $k$, and whenever $\epsilon_k=+1$ infinitely often one has $\limsup_{N\to\infty}D_N(1/x_\epsilon)\ge\tfrac12$.

*Proof.* Lemma D2.4 ($D_k^\epsilon\ge b^{m_k}-1$, $T_k^\epsilon\ge m_k$, $m_{k+1}/m_k\to\infty$) and part (a) hold for either sign. For $\epsilon_K=+1$, the computation of Lemma D2.1 with $\sum_j(-1)^jb^{-jm}$ (kernel-verified in `NormalReciprocalCore.signed_band_identity`) gives

```math
b^nR^\epsilon_K\equiv\Bigl(\sum_{j\le i}(-1)^j\Bigr)b^rR^\epsilon_{K-1}+(-1)^{i+1}\frac{b^rR^\epsilon_{K-1}}{b^m+1}\pmod1 .
```

The multiplier is $0$ in every odd band $i\in\{1,3,\dots,2J-1\}$. Count the $J(m_K-L)$ indices $n=im_K+r$ in odd bands with $0\le r\le m_K-L-1$ (if $L\ge m_K$ or $3b^{-L}\ge1$, part 1 is trivial). Every such index satisfies $n\le2Jm_K-L-1\le m_{K+1}-L-7$, so $|b^n(1/x_\epsilon-R_K^\epsilon)|\le32b^{n-m_{K+1}}\le32b^{-7}b^{-L}\le\tfrac14b^{-L}$ (valid for either sign of the tail, since $m_{K+1}\ge8$), while $b^nR_K^\epsilon\equiv\frac{b^rR_{K-1}^\epsilon}{b^{m_K}+1}\in(0,4b^{r-m_K}]\subseteq(0,2b^{-L}]$. Hence all $J(m_K-L)$ points lie in the two-sided circle arc $[-\tfrac14b^{-L},\tfrac94b^{-L})$ of length $\tfrac52b^{-L}<3b^{-L}$, yielding part 1 directly. Taking $J=1$ and $L=\lfloor\sqrt{m_K}\rfloor$ along any infinite subsequence with $\epsilon_K=+1$ (since $2m_K\le m_{K+1}-6$ holds for large $K$ by $m_{K+1}/m_K\to\infty$) gives $\limsup D_N(1/x_\epsilon)\ge\tfrac12$.

For the converse in 2, let $\epsilon_k=-1$ for $k\ge k_0$. Lemmas D2.1–D2.2, Proposition D2.3, and the Erdős–Turán proof of Theorem D2(b) need only the windows $K-1,K$ with $K\ge k_0+2$; the factors before $k_0$ enter only through $D_{K-2}^\epsilon\to\infty$. $\square$

For $b=2$ and $m=(2,8,160,\ldots)$ with $\epsilon\equiv+1$, the orders are $T'=(4,16,320)$. The script finds $D_N(1/x')=0.66894$ at $N=2Jm_3$ for $J=5,50,200$, with 47% of the points in $[0,2^{-20})$.

### 5.6 What the brief's routes do and do not give

- **The lock principle is right.** On a zero run of $x$ after position $m$, $1/x$ follows the rational $1/x_{\le m}$. Lemma D2.1 is the exact form of this principle for products.
- **Large-order prime-power denominators are the wrong lever.** Right after a perturbation at $m$, the controlling denominator has size about $b^m$, while the prefix length is about $m$. Equidistribution would then be needed for orbit segments whose length is logarithmic in the modulus, and no estimate of this kind is known: Korobov-type bounds need length at least $(\text{modulus})^\varepsilon$. This is an explanation, **not** an impossibility theorem.
- **The construction does the opposite.** Its denominators have **small** order ($T_3=2160$ against $D_3\approx1.3\cdot10^{16}$). Each window consists of complete periods only, because $T_{K-1}\mid m_K$. The band multipliers $i+1$ run through all residues modulo $D_{K-2}$, and this makes the Fourier coefficients vanish exactly.
- **The rate is genuinely slow.** For $h=D_{K-2}$ every term in step (3) survives. A sketch: on the initial part of window $K$ one gets $|W_{D_{K-2}}(N)|\ge\tfrac12$, so $D_N(y)\ge1/(4\pi D_{K-2})$ by Koksma's inequality. In terms of $N$ this is an iterated-logarithm rate. The script sees $|W_{45}(N)|=0.89$–$0.93$ throughout window 4 of the $b=2$ example ($D_2=45$), while $|W_h(N)|\le2\cdot10^{-4}$ for $h=1,2,3$ at every reported $N\ge2\cdot10^5$.
- **Literature.** Bergelson–Downarowicz (cited in Phase 20) exhibit two kernel elements with a normal product. Theorem D2 is a reciprocal analogue with explicit numbers. No literature search was made for this specific statement, and no novelty claim is made.
- **Euler's product itself.** Theorem D2 is consistent with the conjecture that $P_b=1/E_b$ is normal (Phase 20, §2.5, open), which would give another example with $x=E_b\in K_b$. Nothing here bears on that conjecture.

## 6. Lean finite cores (verified core in `NormalReciprocalCore.lean` + remaining targets)

The core finite algebraic, harmonic, and periodicity statements from D1–D2 are formalized, compiled with zero warnings, and kernel-replayed (`leanchecker`) in [`NormalityChecker/NormalReciprocalCore.lean`](../../NormalityChecker/NormalReciprocalCore.lean):

- `band_identity` (Lemma D2.1): exact rational band identity for `b^(i*m+r) * (R * b^m / (b^m - 1))`.
- `signed_band_identity` (Proposition D2.5): exact alternating-sign band identity showing odd-band multiplier vanishing for `1/(1 + b^(-m))`.
- `sum_residues_cexp_eq_zero` (Lemma D2.2): `∑ c : ZMod D, Complex.exp (2 * π * I * (c.val * k * u) / D) = 0` for `[NeZero D]`, `Nat.Coprime u D`, `¬ D ∣ k`.
- `eulerAutomatonStep_bijective` and `eulerAutomaton_purely_periodic` (Theorem D1.1): pure periodicity of the finite automaton on `ZMod L × ZMod d` whenever `Nat.Coprime b d`.

The remaining finite statements below are blueprint targets for future formalization (`radixDiscrepancy`, `farCount`, and `discrepancy_deficit_le` are existing Phase 18–20 declarations):

```lean
namespace NormalityChecker.EulerScalings

/-- D1: The integral head of `E_b` at `P_k^+`, reduced mod `d`, follows the automaton. -/
theorem eulerHead_pentPlus_mod (b d k : ℕ) (hk : 1 ≤ k) :
    ((eulerHead b (pentPlus k) : ℤ) : ZMod d) =
      eulerStep b k ((eulerHead b (pentPlus (k - 1)) : ℤ) : ZMod d)

/-- Atomic discrepancy of a law on `ZMod d`: a finite max over atom arcs. -/
def atomicDisc (d : ℕ) [NeZero d] (w : ZMod d → ℚ) : ℚ := sorry -- finite max, decidable

/-- Lemma 1.1 (atomic limit lemma). -/
theorem abs_discrepancy_sub_atomicDisc_le (b : ℕ) (z : ℝ) {N d : ℕ} (hN : 0 < N) [NeZero d]
    (α : ℕ → ZMod d) (G : Finset ℕ) (hG : G ⊆ Finset.range N) {η : ℝ}
    (hη : 0 ≤ η ∧ η < 1 / (4 * d))
    -- `circleDist` is the distance in ℝ/ℤ (to be defined from `Int.fract`)
    (hnear : ∀ n ∈ G, circleDist ((b : ℝ) ^ n * z) ((α n).val / d) ≤ η)
    (w : ZMod d → ℚ) (hw0 : ∀ j, 0 ≤ w j) (hw : ∑ j, w j = 1) :
    |radixDiscrepancy b z N - atomicDisc d w| ≤
      (∑ j, |((G.filter (α · = j)).card : ℝ) / N - w j|) + (1 - G.card / N) + 2 * η

/-- Lemma 1.2 (runs): visit counts along `u b^i`, `i < g`, are within the orbit size. -/
theorem run_counts_l1_le (b : ℕ) {d : ℕ} [NeZero d] (u : ZMod d) (g : ℕ) (hb : IsUnit (b : ZMod d)) :
    ∑ j, |(((Finset.range g).filter (fun i => u * b ^ i = j)).card : ℚ) - g * orbitLaw b u j|
      ≤ orderOf (b : ZMod d)

/-- D1.4: Frobenius, `E(q)^2 ≡ E(q^2) (mod 2)` coefficientwise. -/
theorem eulerSeries_sq_mod_two :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (eulerSeries ^ 2) =
      PowerSeries.map (Int.castRingHom (ZMod 2)) (PowerSeries.subst (X ^ 2) eulerSeries)

/-- D2(a): products `∏ (1 - b^{-m_k})` with subset-sum support are in the kernel. -/
theorem lacunaryProduct_discrepancy_tendsto_one (b : ℕ) (hb : 2 ≤ b) (m : ℕ → ℕ)
    (hgrowth : Tendsto (fun k => (m (k+1) : ℝ) / m k) atTop atTop) :
    Tendsto (fun N => radixDiscrepancy b (lacunaryProduct b m) N) atTop (𝓝 1)
```

With an Erdős–Turán statement (not yet in Mathlib or this repository), `NormalReciprocalCore.band_identity` and `sum_residues_cexp_eq_zero` plus the finite window inequality of Proposition D2.3 would give Theorem D2(b) in Lean. The `sorry` in `atomicDisc` marks a blueprint definition to be written, not a gap in a proof.

## 7. Verification record

```sh
python -B scripts/phase21_euler_reciprocals.py
```

Standard library only. The run takes about 7 s, performs 13,086 checks and exits 0. It verifies:

- **D1 automata.** All automata and limit laws for $E_b$ and $E_b^3$ in 15 cases $(b,d)$ and all admissible numerators $a$. Masses equal 1, laws are $\times b$-invariant, and $1/d\le D^*<1$. The Phase 20 values hold, the primitive-root closed form holds (12 cases, both series), the numerator dependence is as stated, and $d\mid2k+1$ holds for at most one class of $k\bmod d$.
- **D1 finite inequality.** The inequality of Lemma 1.1 holds at $N=2^{12},2^{14},2^{16}$ for 9 multiples of $E_b$ and 5 of $E_b^3$. The orbit points come from exact residues plus a 60–80-bit integer window, with explicit tail bounds.
- **D1 for $E_b^2$.** Frobenius holds through $q^{20000}$, as does the law $(\tfrac13,\tfrac23)$ of $E(b^{-2})/2$. The residue sequences of $E_3^2$ and $E(3^{-2})$ agree modulo 2 below $2^{17}$, and the finite inequality holds for $E_3^2/2$ and for $E_b^2/d$ with $d$ odd. The script also checks $a_2(n)=\pm2^\omega$ on $S'$ below $2^{15}$ and records the alternation functionals.
- **D2.** The orders $2,12,2160$ and the growth inequality hold. The band identity is checked in exact rational arithmetic, including $R_4$ with $m_4=43200$ (43,254-bit denominator). Cycle Fourier coefficients vanish to $10^{-9}$ off $D_{K-1}\mathbb Z$, in bases 2 and 3. $|W_h(N)|$ satisfies the explicit window bound for $h\in\{1,2,3,5,9,45\}$ at 11 cutoffs up to $2^{19}$. $D_{2^{19}}(1/x)=0.054$, and $1-D_N(x)\le2/N+(w+1)S(N+w)/N$ holds (at $2^{19}$: $1.5\cdot10^{-4}$ against the bound $1.2\cdot10^{-3}$). For the contrast product, the band identity and $D_N(1/x')\ge\tfrac12-L/m$ hold.

All finite values are measurements at accessible scales. They test the stated identities and finite inequalities; they are not evidence for asymptotic constants.

## 8. Open problems

1. The limit law of $\tfrac adE_b^2$ for odd $d>1$, or even the existence of $\lim D_N$; the finite data suggest the uniform law for prime $d$. A complete write-up of Lemma S.
2. A matching lower bound $|D_N(\tfrac adE_b)-D_\infty|\gg\log N/\sqrt N$ along a subsequence, or the exact second-order term.
3. An irrational $x\in K_b$ with $D_N(1/x)=O(N^{-c})$, or a proof that $x\in K_b$ forces a slow rate for $1/x$. Theorem D2 gives only an iterated-logarithm rate, and for this family that slowness is genuine (§5.6).
4. Normality of $P_b=1/E_b$ (Phase 20).
5. Whether $1/x$ can be normal for $x\in K_b$ whose limit point $c\in F_b$ is nonzero, for example $x\in\tfrac1{b-1}+\{w:M_N(w)\to0\}$. The construction above has $c=0$; the band method should adapt, but this has not been checked.
