# Short orbits on growing moduli, and irrationality exponents (Tracks C3–C4)

Notation follows [nonlinear-boundary.md](../phase21/nonlinear-boundary.md) and [multivariate-and-dense-allprime.md](../phase21/multivariate-and-dense-allprime.md). Throughout, $b\ge2$, $p$ is an odd prime with $p\nmid b$, $t=\operatorname{ord}_pb$, $a_0=v_p(b^t-1)\ge1$, and $e(x)=\exp(2\pi ix)$. For an integer $G\equiv1\pmod p$ with $G\ne1$ write $A(G)=v_p(G-1)$. $C=C(b,p,s,d)=\sum_{i\ge1}p^{-sv_p(i)}b^{-ti^d}$, and $\mu(\xi)$ is the irrationality exponent of a real number $\xi$.

## Summary

| Item | Result | Evidence |
|---|---|---|
| C3, input | **Lemma A.** For $p$ odd, a principal unit $G$ and $p\nmid c$, $\lvert\sum_{m<M}e(cG^m/p^e)\rvert\le9M_0^{1-\delta}$ whenever $M\le M_0$, $M_0\ge M_*=p^{\lceil2/\theta\rceil+9}$, $p^{\theta e}\le M_0$, $A(G)<e$ and $A(G)\le\frac3{16}\log_pM_0-1$. The saving $\delta=2^{-\lceil2/\theta\rceil-3}$ and the constant 9 do not depend on $G$. A bound on $A(G)$ of order $\log_pM_0$ is necessary | Proof (§1). The sharpness example and the LTE, vanishing and differencing identities are checked exactly in the script |
| C3, reduction | **Corollary B.** For $y=a/(p^eQ)$, splitting $j$ modulo $\tau=\operatorname{lcm}(t,\operatorname{ord}_Qb)$ reduces $\sum_{j<T}e(b^jy)$ to $\tau$ sums of Lemma A with base $G=b^\tau$. Here $A(G)=a_0+v_p(\operatorname{ord}_Qb)$. **Lemma D** bounds the largest auxiliary prime: $\log\ell_{\max}\ll\log M/\log\log M$ with $M=\operatorname{ord}_\Lambda b$ | Proofs (§2). The exact factorization and the LTE identity are checked on Theorem H prefixes with $d=3,4,5,6$ and on all 243 divisors of $\prod\ell^2$ |
| C3.1 | **Theorem E.** $D_N(P(C);b)\ll_P(\log\log N)^{-d/(d-1)}$ for every $d\ge r+1$ when $\deg P=r\ge2$, and $\ll_PN^{-\eta}$ when $r=1$. This removes the hypothesis $d>r(s+1)$ of Corollary Q1 | Proof (§3) |
| C3.2 | **Theorem H′.** Theorem H holds for every $d\ge r+1$. The auxiliary support may grow like a power of $N$, provided $\limsup_K\log\operatorname{ord}_{\Lambda_K^r}(b)/\log K<d-r$ | Proof (§4) |
| C3, positions | For degree $\le r$ on the schedule $tk^d$, the $j$-th prime may first appear at a position $n_j$ with $\log n_j\ge(\frac{(r-1)d}{d-r}+\epsilon)j\log j$ ($r\ge2$), or $\log n_j\ge(\frac d{d-1}+\epsilon)\log A_b(\ell_j)$, where $\log A_b(\ell_j)\ll j\log\log j$ ($r=1$) | §4 |
| C4, ratio $\to1$ | For Theorems H and U, truncation separation gives only $\lvert W-A/Q\rvert\ge Q^{-\psi(Q)}$ with $\psi(Q)\to\infty$: $\psi\asymp(\log Q)^{1/(d-1)}$ (H) and $\psi=\exp((1+o(1))\sqrt{\log\log Q})$ (U). Whether $\mu(W)<\infty$ is **open** | Proof (§5) |
| C4, finite exponent, degree $\le r$ | **Theorem G.** Take a geometric schedule $n_k=t\lambda^k$ with integer $\lambda\ge r+1$, linear weights $p^{-k}$, $p>(r+1)!$, and sparse auxiliary primes with units $\equiv1\bmod p$. Then $W$ is all-prime, $P(W)$ is normal with $D_N\ll N^{-\eta}$ for $\deg P\le r$, and $\mu(W)=\lambda$ when $\lambda\ge3$ | Proof (§6). Exact $p$-adic depth at all 145 insertion positions tested, exact denominators, convergents |
| C4, finite exponent, all degrees | **Theorem S.** Use the Stoneham schedule $b^{-p^k}$, weights $p^{-k}$ and auxiliary primes with units $\equiv1\bmod p^j$. Then $W$ is all-prime, $P(W)$ is normal for **every** nonconstant $P$, and $\mu(W)=p$. This uses the Phase 13/14 periodic pole retention as input | Proof (§7). In the script: bounded depth defects for $d=2,\ldots,5$, and the exact congruence with $\alpha_{2,3}$ modulo $3^l$ with auxiliary primes inside the active window |
| Obstacles | Base-$(r+1)$ weights make the denominators super-exponential in the run length. A new prime at every index of a geometric schedule fails the complete-period budget, and numerically exceeds the budget of Corollary B. The bound $\lambda>r$ suffices, so $\lambda>r+1$ is not needed. Ties cancel when $p\le(r+1)!$ | §8 |

[Exact checks](../../scripts/phase22_short_orbits.py)

## 1. A uniform short-orbit bound for principal units

**What the repository already has.** [`NormalityChecker/SmoothOrbit.lean`](../../NormalityChecker/SmoothOrbit.lean) proves `fixed_support_orbit_estimate`. The statement `SmoothOrbitEstimate b c` reads: for all $d$ and $\eta>0$ there is $M$ such that every $y$ with $M\le\operatorname{den}y\mid c^j$ and $\operatorname{den}y\le T^d$ has $\lvert\sum_{i<T}e(b^iy)\rvert\le\eta T$. The bound is uniform in the numerator and the length. The threshold $M$ is not explicit, and the support $c$ is fixed. The proof differences along strides $v=\operatorname{ord}_Db$ (`difference_den`), and its own comment says it "does not give Vandehey's quantitative savings". [Phase 14](../phase14/quantitative-composites.md#from-reduced-moduli-to-arbitrary-final-cutoffs) uses Vandehey's Theorem 5.1 as an external input,

$$
 \Big\lvert\sum_{i<L}e(ab^i/q)\Big\rvert\le\big(A_kq^{\alpha_k}L^{\gamma_k}+B_kq^{-\alpha_k}L^{\nu_k}\big)(1+\log q)^{2^{-k}},
$$

for $q$ supported on a fixed finite set $S$ of primes coprime to $b$. The constants come from orders and valuations of the base ([audit](../phase13/reviews/quantitative-coverage.md)). That suffices for the fixed-support Theorem E below. It does not apply to bases $b^\tau$ with $\tau\to\infty$, because uniformity in a varying base is not stated there. Lemma A is a self-contained prime-power estimate uniform in the base. It makes the stride differencing of `SmoothOrbit.lean` quantitative by tracking $A(G)$.

**Lemma A.** Let $p$ be an odd prime and $\theta\in(0,1]$. Put $n_\theta=\lceil2/\theta\rceil+1$, $\delta=2^{-2-n_\theta}$ and $M_*=p^{n_\theta+8}$. Suppose $M_0\ge M_*$, $G\equiv1\pmod p$ is an integer, $G\ne1$, and $A=A(G)\le\frac3{16}\log_pM_0-1$. Suppose $e,c\in\mathbb Z$, $A<e\le\theta^{-1}\log_pM_0$ and $p\nmid c$. Then for every integer $0\le M\le M_0$,

$$
 \Big\lvert S(G,e,c;M)\Big\rvert\le9M_0^{1-\delta},\qquad S(G,e,c;M)=\sum_{0\le m<M}e\Big(\frac{cG^m}{p^e}\Big).
$$

*Proof.* Three facts are used. (i) LTE: $v_p(G^n-1)=A+v_p(n)$, since $p$ is odd and $G\equiv1\pmod p$. (ii) Hence $G$ has order $p^{e-A}$ modulo $p^e$ and generates the group $1+p^A\mathbb Z/p^e\mathbb Z$, which has the same order. So for $X:=e-A\ge1$, a complete period gives

$$
 \sum_{z\bmod p^X}e\Big(\frac{c(1+p^Az)}{p^e}\Big)=e\Big(\frac c{p^e}\Big)\sum_{z\bmod p^X}e\Big(\frac{cz}{p^X}\Big)=0,
$$

and therefore $\lvert S\rvert<p^X$ for every length $M$. (iii) The stride van der Corput inequality. For $H,w\ge1$,

$$
 \lvert S\rvert^2\le\frac{M+(H-1)w}{H}\Big(M+2\sum_{h=1}^{H-1}\lvert C_h\rvert\Big),\qquad C_h=\sum_{0\le m<M-hw}e\Big(\frac{c(G^{m+hw}-G^m)}{p^e}\Big).
$$

This is Cauchy–Schwarz applied to $H\cdot S=\sum_n\sum_{i<H}a_{n+iw}$. By (i), $c(G^{hw}-1)=c_hp^{A+v_p(hw)}$ with $p\nmid c_h$. So $C_h=S(G,e_h,c_h;\max(0,M-hw))$ (an empty sum when $M\le hw$) with the **same base** and $e_h=e-A-v_p(hw)$.

Put $L_0=\log_pM_0$, $W=\lfloor\frac34L_0\rfloor$, $\kappa=\lfloor\frac12L_0\rfloor$ and $H=\lfloor M_0^{1/4}\rfloor$, and keep these fixed. Let $\mathcal F$ be the set of triples $(G,e,c)$ with $A(G)\le W/4$, $e-A(G)\ge1$ and $p\nmid c$. We prove by induction on $n\ge0$:

> **Claim($n$).** If $(G,e,c)\in\mathcal F$ and $X=e-A\le W+n\kappa$, then $\lvert S(G,e,c;M)\rvert\le C_nM_0^{1-\delta_n}$ for all $0\le M\le M_0$. Here $C_0=1$, $C_{n+1}=(4+8C_n)^{1/2}\le9$, $\delta_n=2^{-2-n}$.

*Base.* If $X\le W$, then (ii) gives $\lvert S\rvert<p^W\le M_0^{3/4}$.

*Step.* Let $W+n\kappa<X\le W+(n+1)\kappa$ (smaller $X$ is covered by Claim($n$), since $C_n\le C_{n+1}$ and $\delta_n\ge\delta_{n+1}$). Choose the stride exponent $k\in[0,\kappa]$:

- $k=0$ if $X-A\le W$;
- $k=X-A-W$ if $W<X-A\le W+\kappa$;
- $k=\kappa$ if $X-A>W+\kappa$.

Then $X_1:=X-A-k$ satisfies $\frac34W\le X_1\le W+n\kappa$. In the first case this uses $A\le W/4$. In the last case it uses $X\le W+(n+1)\kappa$ and $A\ge1$. Take $w=p^k\le M_0^{1/2}$. For $1\le h<H$ put $j=v_p(h)\le\frac14L_0$. The differenced triple $(G,e_h,c_h)$ has excess $X_h=e_h-A=X_1-j$, which satisfies

$$
 1\le\tfrac{5}{16}L_0-\tfrac34\le\tfrac34W-\tfrac14L_0\le X_h\le W+n\kappa ,
$$

using $L_0\ge8$. So every $C_h$ falls under Claim($n$), and no shift is lost to a large $v_p(h)$. Since $M+(H-1)w\le2M_0$ and $H\ge\frac12M_0^{1/4}$,

$$
 \lvert S\rvert^2\le4M_0^{3/4}\big(M_0+2HC_nM_0^{1-\delta_n}\big)\le(4+8C_n)M_0^{2-\min(1/4,\delta_n)},
$$

so Claim($n+1$) holds with $\delta_{n+1}=\min(\frac18,\frac{\delta_n}2)=2^{-3-n}$.

*Conclusion.* The hypotheses give $A\le W/4$, so $(G,e,c)\in\mathcal F$. Also $e-A<e\le L_0/\theta\le W+n_\theta\kappa$, because $W+n_\theta\kappa\ge\frac34L_0-1+(\frac2\theta+1)(\frac{L_0}2-1)\ge\frac{L_0}\theta+\frac54L_0-n_\theta-1$ and $L_0\ge n_\theta+8$. Apply Claim($n_\theta$). $\square$

**Necessity of a bound on $A(G)$.** Let $G=1+p^a$, $e=2a$ and $c=1$. Then $G^m\equiv1+mp^a\pmod{p^{2a}}$ and $S=e(p^{-2a})\sum_{m<M}e(m/p^a)$. For $M=\lfloor p^a/10\rfloor$ every phase lies in $[0,\frac1{10})$, so $\lvert S\rvert/M>0.98$, although $M\ge p^{e/2-3}$. In this example $A=\log_p(10M)$. So no estimate uniform in the base can allow $A\ge\log_pM+O(1)$. Lemma A allows $A\le\frac3{16}\log_pM_0-1$. The script checks the example for $(p,a)=(3,6),(5,4),(7,3)$.

A condition of the form $A(G)=o(e)$ is the wrong scale in two respects. Lemma A needs only $A\le c\log_pM_0$, and $\log_pM_0\ge\theta e$, so $A=O(e)$ with a small constant is enough. Conversely, a progression shorter than $p^{A}$ can fail completely whatever $e$ is.

## 2. Splitting off the auxiliary modulus

**Corollary B.** Let $y=a/(p^eQ)$ with $\gcd(a,pQ)=1$ and $\gcd(Q,pb)=1$. Put $T_Q=\operatorname{ord}_Qb$, $\tau=\operatorname{lcm}(t,T_Q)$ and $G=b^\tau$. Then

$$
 A(G)=v_p(b^\tau-1)=v_p(b^{tT_Q}-1)=a_0+v_p(T_Q),
$$

and for $T\ge1$, with $M_0=\lceil T/\tau\rceil$,

$$
 \Big\lvert\sum_{j<T}e(b^jy)\Big\rvert\le\tau\max_{p\nmid c,\ M\le M_0}\lvert S(G,e,c;M)\rvert .
$$

If Lemma A applies to $(M_0,G,e)$ and $\tau\le T$, the sum is at most $18\,T\,(\tau/T)^{\delta}$.

*Proof.* By LTE for $x=b^t\equiv1\pmod p$, $v_p(b^{tm}-1)=a_0+v_p(m)$. Both $\tau/t$ and $T_Q$ have the $p$-adic valuation of $T_Q$, because $p\nmid t$. Write $y\equiv a_1/p^e+a_2/Q\pmod1$ by the Chinese remainder theorem, with $p\nmid a_1$. For $j=\tau m+j_0$, $0\le j_0<\tau$, we have $b^{\tau m}\equiv1\pmod Q$, so

$$
 e(b^jy)=e\Big(\frac{b^{j_0}a_2}{Q}\Big)\,e\Big(\frac{(b^{j_0}a_1)G^m}{p^e}\Big),
$$

and $p\nmid b^{j_0}a_1$. Summing over $m<\#\{m:\tau m+j_0<T\}\le M_0$ gives the first bound. The second is $9\tau M_0^{1-\delta}\le9\tau(2T/\tau)^{1-\delta}\le18T^{1-\delta}\tau^\delta$. $\square$

**The size of $A(G)$.** If $Q\mid\Lambda^rM'$ with $\Lambda$ a product of primes $\ell\nmid pb$, then $v_p(\operatorname{ord}_{\ell^k}b)=v_p(\operatorname{ord}_\ell b)\le v_p(\ell-1)$, because the kernel of $(\mathbb Z/\ell^k)^\times\to(\mathbb Z/\ell)^\times$ is an $\ell$-group. Hence

$$
 A(G)\le a_0+v_p(\operatorname{ord}_{M'}b)+\max_{\ell\mid\Lambda}\log_p\ell .
$$

When the auxiliary primes are introduced in increasing order, every prime $\ell\le\ell_{\max}$ with $\ell\nmid pb$ divides $\Lambda$. If $\Lambda\le N^{O(1)}$, the prime number theorem gives $\ell_{\max}\le(1+o(1))\log\Lambda$, so $A(G)=O(\log\log N)$. In Theorems H′ and G, however, $\Lambda$ may be much larger than any power of $N$ (for degree 1, $\log\Lambda_{k_j}\sim j\log j$ while $\log N$ can be $\asymp j(\log\log j)^2$), and only $\operatorname{ord}_\Lambda b\le N$ is available. The following lemma covers that case.

**Lemma D (largest auxiliary prime).** For $x\ge2$ put $A_b(x)=\operatorname{lcm}\{\operatorname{ord}_\ell b:\ \ell\le x\text{ prime},\ \ell\nmid pb\}$. Then $\log x\ll_b\log A_b(x)/\log\log A_b(x)$ for $x\ge x_0(b)$. Consequently, if $\Lambda$ is squarefree and contains every prime $\ell\le\ell_{\max}$ with $\ell\nmid pb$, then $\operatorname{ord}_\Lambda b=A_b(\ell_{\max})$ and

$$
 A(G)\le a_0+v_p(\operatorname{ord}_{M'}b)+O_b\Big(\frac{\log\operatorname{ord}_\Lambda b}{\log\log\operatorname{ord}_\Lambda b}\Big).
$$

*Proof.* Put $M=A_b(x)$. A prime $\ell$ with $\operatorname{ord}_\ell b=m$ divides $b^m-1$, which has at most $m\log_2b$ prime factors. So at most $\sum_{m\le x^{1/3}}m\log_2b\le x^{2/3}\log_2b$ primes $\ell\le x$ have order $\le x^{1/3}$. Every other prime $\ell\le x$ with $\ell\nmid pb$ has order $m>x^{1/3}$ with $m\mid M$ and $\ell\equiv1\pmod m$, and each such $m$ admits fewer than $x/m<x^{2/3}$ primes $\ell\le x$. Hence $\pi(x)-2-x^{2/3}\log_2b\le d(M)\,x^{2/3}$, so $d(M)\ge x^{1/3}/(2\log x)$ for $x\ge x_0(b)$. The divisor bound $\log d(M)\le(\log2+o(1))\log M/\log\log M$ gives the claim. The bound on $A(G)$ follows from the previous display. $\square$

Under $\operatorname{ord}_\Lambda b\le N$ this gives $A(G)=O(\log N/\log\log N)$, which is $o(\log_pM_0)$ whenever $M_0\ge N^{c}$ for a fixed $c>0$. That is again inside the range of Lemma A. The script checks the identity $A(G)=1+v_3(T_Q)$ for $b=2$, $p=3$ on every divisor of $(7\cdot19\cdot73\cdot37\cdot5)^2$, where $v_3(T_Q)\in\{0,1,2\}$. It also checks the exact CRT factorization of the orbit sum on actual Theorem H prefixes of $W^2$.

## 3. The effective rate for all $d\ge r+1$ (C3.1)

**Theorem E.** Let $s\ge1$, $r\ge1$, $d\ge r+1$, and let $P\in\mathbb Q[x]$ have degree $r$. Then

$$
 D_N(P(C(b,p,s,d));b)\ll_P(\log\log N)^{-d/(d-1)}\quad(r\ge2),\qquad D_N(P(C);b)\ll_PN^{-\eta}\quad(r=1),
$$

with $\eta=\eta(p,s,d)>0$.

*Proof.* Clear denominators and use the setup of [Corollary Q1](../phase21/nonlinear-boundary.md#5-effective-discrepancy-and-what-blocks-more). The shifted prefixes $R_n$ have denominators $q_n\mid p^{rsJ+O_P(1)}M'$ with $M'$ fixed, prime to $pb$. Take the precision $L=\lfloor c_0\log N\rfloor$ with $c_0\log p\le rs/(8d)$, $(c_0\log p)/s<r/d$ and $c_0(1+d/s)\log p<1/2$. The last condition is the freezing condition of Corollary Q1: it puts every shift of the unfrozen shells $J<J_0(L)=\lceil L/s+L/d\rceil$ below $\sqrt N$ for large $N$. Fix $\epsilon_1=1/(6d)$. Steps 1, 2 and 5 of Corollary Q1 (freezing, failed shifts, buffers) do not use $d>r(s+1)$ and are kept. Steps 3–4, the mesh and the complete periods, are replaced as follows.

1. *Runs.* Cut $[1,N]$ at the insertion positions, at the shell boundaries $tp^{dJ}$ and at the $O(\log N\,L^{r-1}p^{L/s})=O(N^{r/d})$ cell boundaries of $M_r\bmod p^L$. That gives $O(N^{r/d})$ runs. On a run $[n_0,n_0+T)$ one has $R_{n_0+j}\equiv b^jR_{n_0}\pmod1$, so $q_n$ is constant along the run, and so is the failure status. Discard four kinds of shift. Failed runs number at most $CN(\log L)^{-d/(d-1)}$ shifts, by Theorem Q. Runs of length $<N^{1-r/d-\epsilon_1}$ cover $O(N^{1-\epsilon_1})$ shifts. Shifts $n<\sqrt N$ number at most $\sqrt N$. The final buffer of length $\lceil2\log_bN\rceil$ of each run costs $O(N^{r/d}\log N)$ in all. Off the buffers the real tail is at most $N^{-1}$.
2. *Erdős–Turán on a retained run.* Let $H_{\rm ET}=\lceil N^{\eta_0}\rceil$ with $0<\eta_0\le\min(\frac12,\frac{rs}{8d})$. In the count form used in [Phase 14](../phase14/quantitative-composites.md#from-reduced-moduli-to-arbitrary-final-cutoffs),
   $$
    T\,D(\text{run})\le4\Big(\frac T{H_{\rm ET}+1}+\sum_{h\le H_{\rm ET}}\frac1h\Big(\Big\lvert\sum_{j<T}e(hb^jR_{n_0})\Big\rvert+\frac{2\pi hT}N\Big)\Big).
   $$
3. *The exponential sum.* The reduced form of $hR_{n_0}$ is $a/(p^eQ')$ with $Q'\mid M'$ and $e=v_p(q_{n_0})-v_p(h)$. On a retained run in shell $J$, $v_p(q_{n_0})\ge rsJ-L+1-O(1)$ with $rsJ\ge\frac{rs}{2d}\log_pN-O(1)$, so $e\ge\frac{rs}{4d}\log_pN-O(1)$, which exceeds $A(G)\le a_0+v_p(\operatorname{ord}_{M'}b)$. Also $e\le\frac{rs}d\log_pN+O(1)$, while $M_0\ge T/\tau\gg N^{1-r/d-\epsilon_1}$ because the stride $\tau=\operatorname{lcm}(t,\operatorname{ord}_{Q'}b)\le t\operatorname{ord}_{M'}b=O(1)$. So $p^{\theta e}\le M_0$ with
   $$
    \theta=\min\Big(1,\frac{d-r-3d\epsilon_1}{rs}\Big)=\min\Big(1,\frac{d-r-1/2}{rs}\Big)\ \ge\ \frac1{2rs}>0 ,
   $$
   and this is exactly where $d\ge r+1$ enters. Corollary B and Lemma A give $\lvert\sum_{j<T}e(hb^jR_{n_0})\rvert\le C\,T^{1-\delta}$, uniformly in $h\le H_{\rm ET}$. The gcd of $h$ with $q_{n_0}$ costs only $v_p(h)\le\eta_0\log_pN$ in $e$.
4. *Summation.* Since $T\ge N^{1-r/d-\epsilon_1}\ge N^{1/(2d)}$, each retained run has $D(\text{run})\ll N^{-\eta_0}+N^{-\delta/(2d)}\log N+N^{\eta_0-1}$.

Adding the discarded shifts gives the stated bound for $r\ge2$. For $r=1$ the frozen residue is $A\lfloor u^{1/d}\rfloor\not\equiv0\pmod{p^{v_p(A)+1}}$, so no shift fails, and every term is a power of $N$. $\square$

The exponents are poor: $\delta=2^{-\lceil2/\theta\rceil-3}$, for example $2^{-19}$ at $(r,s,d)=(2,2,3)$ (table in the script). They affect only the error terms other than the failed shifts. The rate $(\log\log N)^{-d/(d-1)}$ comes from Theorem Q alone. Vandehey's Theorem 5.1, with the fixed support $S=\{p\}\cup\{\ell\mid M'\}$, would give better $\delta$ in step 3. The conditional sentence after Corollary Q1 ("any short-orbit bound … explicit for $T\ge p^{\theta e}$ … would extend Corollary Q1 to the whole range") is thereby discharged.

## 4. Theorem H for all $d\ge r+1$, and larger auxiliary support (C3.2)

**Theorem H′.** Let $s\ge1$, $r\ge1$, $d\ge r+1$. Let $W=\sum_kp^{-sv_p(k)}\mu_k^{-1}b^{-tk^d}$ be as in [Theorem H](../phase21/multivariate-and-dense-allprime.md#6-the-hybrid-on-a-polynomial-schedule): the primes $\ell_1<\ell_2<\cdots$ not dividing $pb$ sit at strictly increasing indices $k_j$ with $p\nmid k_j$, and $\Lambda_K=\prod_{k_j\le K}\ell_j$. Replace the hypothesis $\log\Lambda_K=o(\log K)$ by

$$
 (\mathrm P_H)\qquad\limsup_{K\to\infty}\frac{\log\operatorname{ord}_{\Lambda_K^r}(b)}{\log K}<d-r .
$$

Then both conclusions of Theorem H hold. Every off-radix prime divides the reduced shifted prefix denominators of $W$ from some point on. For $1\le\deg P\le r$, $P(W)$ is normal, with $D_N\ll_P(\log\log N)^{-d/(d-1)}$ if $\deg P\ge2$ and $D_N\ll_PN^{-\eta}$ if $\deg P=1$. In particular the original hypothesis $\log\Lambda_K=o(\log K)$ suffices for every $d\ge r+1$.

*Proof.* Part (1) and the $p$-adic part (frozen residues, Theorem Q, the hypothesis $p\nmid k_j$) are unchanged from Theorem H. The run count $O(N^{r/d})$ and the tail are unchanged, since the auxiliary coefficients have modulus $\le1$. Run the proof of Theorem E, with the same constraints on $c_0$ and $\eta_0$, and with $Q'\mid\Lambda_K^rM'$, $K=K(N)$. Choose $\epsilon_1>0$ with $\log\operatorname{ord}_{\Lambda_K^r}(b)\le(d-r-5d\epsilon_1)\log K$ for large $K$. Since $N\ge tK^d$, this gives a stride $\tau=\operatorname{lcm}(t,\operatorname{ord}_{Q'}b)\le N^{1-r/d-4\epsilon_1}$, and so $M_0\ge T/\tau\ge N^{\epsilon_1}$ on runs of length $\ge N^{1-r/d-\epsilon_1}$. Lemma A applies to the base $G=b^\tau$ with these parameters.

- $A(G)=O(\log N/\log\log N)\le\frac3{16}\log_pM_0-1$ by Lemma D, because $\operatorname{ord}_{\Lambda_K}b\le\operatorname{ord}_{\Lambda_K^r}b\le N$ and $\Lambda_K$ contains every prime $\ell\le\ell_{\max}$ with $\ell\nmid pb$.
- $p^{\theta e}\le M_0$ with $\theta=\min(1,d\epsilon_1/(2rs))$, because $e\le\frac{rs}d\log_pN+O(1)$ (as $\Lambda_K$ is prime to $p$).
- $e\ge\frac{rs}{4d}\log_pN-O(1)>A(G)$.

Corollary B bounds each run sum by $18T(\tau/T)^\delta\le18TN^{-\epsilon_1\delta}$. The rest is as in Theorem E. $\square$

For squarefree $\Lambda$ one has $\operatorname{ord}_{\Lambda^r}(b)\le\Lambda^{r-1}A_b(\ell_{\max})$, where $A_b(x)\le A(x)=\operatorname{lcm}_{\ell\le x}(\ell-1)$. Phase 19 used $\log A(x)\ll x\log\log x\log\log\log x/\log x$; an upper-bound sieve gives $\log A(x)\ll x\log\log x/\log x$. Indeed, prime powers $q^a\mid A(x)$ with $q\le x/\log x$ contribute at most $\pi(\sqrt x)\log x+\theta(x/\log x)\ll x/\log x$. A prime $q>x/\log x$ divides $A(x)$ only if $mq+1$ is prime for some $m<\log x$. The Selberg sieve bounds the number of $q\le x/m$ with $q$ and $mq+1$ both prime by $\ll\frac{x}{m(\log x)^2}\frac m{\varphi(m)}$. So these $q$ contribute $\ll\sum_{m<\log x}\frac{x}{\varphi(m)\log x}\ll\frac{x\log\log x}{\log x}$. No matching lower bound is proved here. With all primes introduced in order, $\log\Lambda_{k_j}\sim\ell_j\sim j\log j$. So ($\mathrm P_H$) holds when

$$
 \log k_j\ \ge\ \Big(\frac{r-1}{d-r}+\epsilon\Big)j\log j\quad(r\ge2),\qquad \log k_j\ \ge\ \Big(\frac1{d-1}+\epsilon\Big)\log A_b(\ell_j)\quad(r=1).
$$

| Construction | Position $n_j$ of the $j$-th prime |
|---|---|
| Theorem H (Phase 21) | $\log n_j/(j\log j)\to\infty$ |
| Theorem H′, degree $\le r$, $r\ge2$ | $\log n_j\ge(\frac{(r-1)d}{d-r}+\epsilon)j\log j$ |
| Theorem H′, degree 1 | $\log n_j\ge(\frac d{d-1}+\epsilon)\log A_b(\ell_j)$, where $\log A_b(\ell_j)\ll j\log\log j$ |
| Theorem G, degree $\le r$, $r\ge2$ | $\log n_j\ge(1+\epsilon)(r-1)j\log j$ (from $(\mathrm P_G)$, §6) |

The cruder budget $\log\Lambda_K\le(\frac{1-r/d}r-\epsilon)\log N$ comes from $T_Q\le\Lambda_K^r$. It is sufficient, but $\operatorname{ord}_{\ell^r}b\mid\ell^{r-1}\operatorname{ord}_\ell b$ improves it to $(r-1)\log\Lambda_K+\log A_b<(1-\frac rd)\log N$. For degree $\ge2$ the order of magnitude $j\log j$ remains. The method needs $\tau\le T^{1-\eta}$, and $\operatorname{ord}_{\Lambda^r}(b)\ge\Lambda^{r-1}$ whenever $\Lambda$ is odd, $\Lambda^r$ divides the reduced denominator, and no $\ell\mid\Lambda$ is a base-$b$ Wieferich prime. If $2\mid\Lambda$ and $r\ge3$, the factor $2^{r-1}$ drops to $2^{r-2}$, which gives $\ge\frac12\Lambda^{r-1}$. Below that threshold the sum is a short orbit on a growing composite modulus with no fixed prime-power part to exploit. These thresholds are sufficient and are not proved necessary.

## 5. Irrationality exponents when consecutive ratios tend to 1

**Lemma T (truncation separation).** Let $\xi=\sum_kc_kb^{-n_k}$ with $0<c_k\le C$ rational and $n_k$ strictly increasing integers. Let $U_k$ be the prefixes, and suppose $\operatorname{den}U_k\mid D_kb^{n_k}$. If $8CQD_k\le b^{n_{k+1}-n_k}$, then either $A/Q=U_k$ or $\lvert\xi-A/Q\rvert\ge1/(2QD_kb^{n_k})$.

*Proof.* We have $0<\xi-U_k\le C\sum_{m\ge n_{k+1}}b^{-m}\le2Cb^{-n_{k+1}}\le1/(4QD_kb^{n_k})$. If $A/Q\ne U_k$, then $\lvert A/Q-U_k\rvert\ge1/(QD_kb^{n_k})$. $\square$

Put $Y_k=b^{n_{k+1}-n_k}/(8CD_k)$ and $\rho_k=n_k/(n_k-n_{k-1})$. For large $Q$ let $k$ be minimal with $Q\le Y_k$. Then $b^{n_k}=(8CD_{k-1}Y_{k-1})^{\rho_k}<(8CD_{k-1}Q)^{\rho_k}$, so

$$
 A/Q\ne U_k\ \Longrightarrow\ \lvert\xi-A/Q\rvert\ \ge\ \big(2D_k(8CD_{k-1})^{\rho_k}\big)^{-1}Q^{-1-\rho_k}. \tag{5.1}
$$

If $A/Q=U_k$ instead, then $Q\ge\operatorname{den}U_k$ and $\lvert\xi-U_k\rvert\ge c_{k+1}b^{-n_{k+1}}$.

**Proposition 5.1.** Let $W$ be the number of Theorem H or Theorem U. In both, $c_k=p^{-sv_p(k)}\mu_k^{-1}\le1$ and $D_k=p^{s\lfloor\log_pk\rfloor}\Lambda_k$. The top coefficient makes $\operatorname{den}U_k=D'_kb^{n_k}\ge b^{n_k}$. So the case $A/Q=U_k$ gives exponent $n_{k+1}/n_k+o(1)\to1$, and (5.1) governs. The result is $\lvert W-A/Q\rvert\ge Q^{-\psi(Q)}$ for large $Q$, with

- Theorem H ($n_k=tk^d$, so $\rho_k\sim k/d$ and $\log Y_{k-1}\sim tdk^{d-1}\log b$): $\psi(Q)=(1+o(1))\frac1d\big(\frac{\log_bQ}{td}\big)^{1/(d-1)}$;
- Theorem U ($n_k=tk\lceil e^{(\log(k+1))^2}\rceil$, so $\rho_k\sim k/(2\log k)$ and $\log Y_{k-1}\sim2t\log k\,e^{(\log k)^2}\log b$): $\psi(Q)=\exp\big((1+o(1))\sqrt{\log\log Q}\big)$. In particular, for every $\epsilon>0$, $\lvert W-A/Q\rvert\ge Q^{-(\log Q)^\epsilon}$ for large $Q$.

*Proof.* Substitute into (5.1). Here $\log D_k=O(\log k)+\log\Lambda_k$, which is $o(n_k-n_{k-1})$ in both cases. For U, $\log\Lambda_K=o((\log K)^2)$. $\square$

Since $\psi(Q)\to\infty$, Proposition 5.1 does not exclude Liouville approximations. It is also the limit of the method. Every separation argument of this kind needs a gap $n_{k+1}-n_k\gg\log Q$ starting at a position $\ll\log Q$. When $n_{k+1}/n_k\to1$, the first gap of length $m$ starts at $m\rho(m)$ with $\rho\to\infty$. The finiteness of $\mu(W)$ for Theorems H and U therefore remains **open**. The script tabulates $\rho_k$: $\rho_{10^4}\approx2000$ for H with $d=5$, and $\approx515$ for U.

## 6. Finite exponent with degree $\le r$: geometric schedules (C4)

**Theorem G.** Let $r\ge1$ and $b\ge2$. Choose a prime $p\nmid b$ with $p>(r+1)!$, put $t=\operatorname{ord}_pb$, fix an integer $\lambda\ge r+1$, and put $n_k=t\lambda^k$. List the primes not dividing $pb$ as $\ell_1<\ell_2<\cdots$. Place $\ell_j$ at strictly increasing indices $k_j\ge j$ with

$$
 (\mathrm P_G)\qquad\limsup_{K\to\infty}\frac{\log\operatorname{ord}_{\Lambda_K^r}(b)}{K\log\lambda}<1,\qquad\Lambda_K=\prod_{k_j\le K}\ell_j .
$$

At $k=k_j$ let $\mu_k=\ell_j$ and let $u_k$ be the least positive integer with $u_k\equiv\ell_j\pmod p$ and $\gcd(u_k,b\ell_j)=1$. Otherwise $\mu_k=u_k=1$. Put

$$
 W=\sum_{k\ge1}\frac{u_k}{p^k\mu_k}\,b^{-n_k}.
$$

1. For $n_K\le n<n_{K+1}$ the reduced shifted prefix denominator of $W$ is $p^K\Lambda_K$. So every prime $\ell\nmid b$ divides it from some point on.
2. For every nonconstant $P\in\mathbb Q[x]$ with $\deg P\le r$, $P(W)$ is normal in base $b$, and $D_N(P(W);b)\ll_PN^{-\eta_P}$.
3. $\lambda\le\mu(W)\le\max(\lambda,\frac{2\lambda-1}{\lambda-1})$. Hence $\mu(W)=\lambda$ when $\lambda\ge3$, and $W$ is then transcendental by Roth's theorem.

The indices $k_j=j+\lceil2(r-1)j\log(j+1)/\log\lambda\rceil$ ($r\ge2$) and $k_j=j\lceil(\log\log(j+16))^2\rceil$ ($r=1$) satisfy $(\mathrm P_G)$. For $r=1$ the script computes the ratio in $(\mathrm P_G)$ with $b=2$, $\lambda=3$ for $20<j\le3000$, and its maximum is $0.595$.

*Proof of (1).* The term at $K$ has $p$-adic valuation exactly $-K$, since $u_K\equiv\ell\not\equiv0$ or $u_K=1$. Earlier terms have valuation $>-K$. The prime $\ell_j$ occurs only at $k_j$, with numerator $u_{k_j}$ prime to $\ell_j$.

*Proof of (2): exact depth.* Replacing $r$ by $\deg P$ preserves $p>(r+1)!$, $\lambda>r$ and $(\mathrm P_G)$ (since $\operatorname{ord}_{\Lambda^{r'}}b\le\operatorname{ord}_{\Lambda^r}b$ for $r'\le r$), so assume $\deg P=r$. Clear denominators: $b^cP(W)=Y(W)/D_0$ with $Y=\sum_aA_ax^a\in\mathbb Z[x]$, $A_r\ne0$, and $\gcd(D_0,b)=1$. Write a degree-$a$ tuple as a sorted multiset $M=(i_1\ge\cdots\ge i_a)$, with position $\pi(M)=\sum n_{i_c}$ and weight $w(M)=\sum i_c$. The prefix at $n$ is $S_a(n)=\sum_{\pi(M)\le n}\binom aM\prod_c\frac{u_{i_c}}{\mu_{i_c}}\,b^{n-\pi(M)}p^{-w(M)}$, where $\binom aM$ counts the orderings.

- *Lex order equals position order.* Let $M<_{\rm lex}M'$ be sorted $r$-multisets with first difference at slot $c$. Then $\pi(M)\le\sum_{c'<c}n_{i'_{c'}}+(r-c+1)n_{i'_c-1}<\pi(M')$, because $r<\lambda$. So the multisets present at $n$ form a lexicographic initial segment $\{M\le_{\rm lex}g\}$, and distinct multisets have distinct positions.
- *Top weight.* If $M<_{\rm lex}g$ first differs from $g$ at slot $c$, then $w(M)\le w(\mathrm{cand}_c)$, with equality only for $M=\mathrm{cand}_c=(g_1,\ldots,g_{c-1},(g_c-1)^{r-c+1})$. Hence the top weight $w^*(n)$ is attained by at most $r+1$ multisets, and the total number of ordered top tuples lies in $[1,(r+1)!]$. For $n\in[n_K,n_{K+1})$, $((K-1)^r)$ is present (as $rn_{K-1}\le n_K$), and all indices are $\le K$. So $r(K-1)\le w^*(n)\le rK$.
- *No cancellation.* Every unit is $\equiv1\pmod p$: $u/\mu\equiv1$, and $b^{-n_i}\equiv1$ because $t\mid n_i$. So the top tuples contribute $p^{-w^*}b^n\cdot(\text{count})\not\equiv0\pmod{p^{-w^*+1}}$, because $p>(r+1)!$. Other degree-$r$ tuples have valuation $\ge-w^*+1$.
- *Lower degrees.* Degree $a<r$ has weights $\le aK\le w^*-((r-a)K-r)$, which is negligible for large $K$.

Hence $v_p(R_n)=-w^*(n)+v_p(A_r)-v_p(D_0)$ for every $n\ge n_{K_0(P)}$, with **no exceptional shifts**. The script verifies this equality at every insertion position of the tested shells: $(r,p,\lambda)=(1,3,3)$, $(2,7,3)$, $(3,29,4)$, 145 positions, with actual units and $b$-powers.

*Proof of (2): digits.* Let $K=K(N)\le\log_\lambda N$. There are at most $(K+2)^r=O((\log N)^r)$ insertion positions in $[1,N]$. The positions $n_k+(r-1)n_1$ are insertions of the degree-$r$ monomial, and consecutive ones have ratio $\le\lambda$. So the shifts before the first insertion after $N^{1-\epsilon}$ number at most $\lambda N^{1-\epsilon}+O(1)$. Runs shorter than $N^{1-\epsilon}$ cover $O(N^{1-\epsilon}(\log N)^r)$ shifts, and the buffers cover $O((\log N)^{r+1})$. On a remaining run starting at $n_0$, put $K_0=K(n_0)\in[(1-\epsilon)\log_\lambda N-O(1),K]$. Then $q=p^{v}Q'$ with $v\in[r(K_0-1)-O(1),rK_0+O(1)]$ and $Q'\mid\Lambda_K^rD'_0$, where $D'_0$ is the prime-to-$p$ part of $D_0$. Apply Erdős–Turán with $H_{\rm ET}=N^{\eta_0}$ and Corollary B. By $(\mathrm P_G)$, $\operatorname{ord}_{\Lambda_K^r}b\le\lambda^{(1-4\epsilon)K}\le N^{1-4\epsilon}$ for small $\epsilon$, so the stride satisfies $\tau\le N^{1-3\epsilon}$ and $M_0\ge N^{\epsilon}$. Then $p^{\theta v}\le M_0$ with $\theta=\epsilon\log\lambda/(2r\log p)$, which is $\le1$ for small $\epsilon$. By Lemma D, $A(G)=O(\log N/\log\log N)\le\frac3{16}\log_pM_0-1$, and $e\ge v-\eta_0\log_pN>A(G)$ for small $\eta_0$. Each long run then has discrepancy $\ll N^{-\epsilon\delta}\log N+N^{-\eta_0}+N^{\eta_0-1}$. $\square$

*Proof of (3).* We have $\operatorname{den}U_k=D_kb^{n_k}$ exactly, with $D_k=p^k\Lambda_k$: the numerator is $\equiv u_k\Lambda_k/\mu_k\pmod{b^{n_k-n_{k-1}}}$, which is prime to $b$. The script confirms this exactly for $k\le8$, $7$, $5$ in the three instances. By the Chinese remainder theorem on the pairwise coprime moduli $p$, $\operatorname{rad}(b)$ and $\ell_j$, the least admissible $u_{k_j}$ is at most $p\operatorname{rad}(b)\ell_j$, so $0<c_k\le\operatorname{rad}(b)=:C$. Since $\Lambda_k\mid b^{\operatorname{ord}_{\Lambda_k}b}-1$, $(\mathrm P_G)$ gives $\log\Lambda_k<\operatorname{ord}_{\Lambda_k}(b)\log b\le\operatorname{ord}_{\Lambda_k^r}(b)\log b\le\lambda^{(1-\epsilon)k}\log b$ for large $k$. Hence $\log D_k=k\log p+\log\Lambda_k=o(\lambda^k)$ and $\log(1/c_{k+1})\le(k+1)\log p+\log\Lambda_{k+1}=o(\lambda^k)$. The stronger statement $\log D_k=O(k)$ is false in general: for the degree-1 schedule above, $\log\Lambda_{k_j}\sim j\log j$ is not $O(k_j)$. *Lower bound:* $\lvert W-U_k\rvert\le2Cb^{-n_{k+1}}=\operatorname{den}(U_k)^{-\lambda+o(1)}$. *Upper bound:* in (5.1), $\rho_k=\lambda/(\lambda-1)$, so $A/Q\ne U_k$ gives exponent $1+\frac\lambda{\lambda-1}+o(1)=\frac{2\lambda-1}{\lambda-1}+o(1)$. If $A/Q=U_k$, then $Q\ge D_kb^{n_k}$ and $\lvert W-U_k\rvert\ge c_{k+1}b^{-\lambda n_k}\ge Q^{-\lambda-o(1)}$. Finally, $\lambda\ge\frac{2\lambda-1}{\lambda-1}$ exactly when $\lambda\ge\frac{3+\sqrt5}2$. $\square$

In the script, $-\log\lvert W-U_k\rvert/\log\operatorname{den}U_k$ rises to $2.9962$ ($\lambda=3$, $k=8$) and $3.9971$ ($\lambda=4$, $k=5$). For $r=1$, $\lambda=3$, the 724 continued-fraction convergents of $U_8$ with $2^{30}\le q\le2\operatorname{den}U_7$ (found among the first 736 partial quotients) all have exponent at most $2.9894$. $U_4,\ldots,U_7$ are among them. This is finite evidence only.

**Remarks.** (a) A real $\lambda>r$ works with $n_k=t\lceil\lambda^k\rceil$, once the sum starts at an index $k_0$ with $\lambda^{k_0}(\lambda-r)>2r$, so that the lexicographic comparison stays strict. Then $\mu(W)=\lambda$ for every real $\lambda\ge\max(r+\epsilon,\frac{3+\sqrt5}2)$. In particular $\mu(W)=\frac{3+\sqrt5}2$ is attained for $r\le2$. (b) The hypothesis $p>(r+1)!$ is used only for non-cancellation at ties, and ties are unavoidable with linear weights. For $r=2$, $p=3$, $\lambda=3$, at $n=n_8+n_6$ the top multisets $(7,7)$ and $(8,6)$ have $1+2=3$ orderings, and the exact valuation is $-13$ instead of $-14$ (script). (c) The method cannot reach all degrees with finite exponent. For $\deg P>\lambda$ it would need $\lambda\to\infty$, and $n_{k+1}/n_k\to\infty$ makes $W$ Liouville via $U_k$.

## 7. Finite exponent for all degrees: the Stoneham schedule

**Theorem S.** Let $b\ge2$ and let $p\nmid b$ be an odd prime. Place the primes $\ell_1<\ell_2<\cdots$ not dividing $pb$ at strictly increasing indices $k_j\ge j$ with $\log\Lambda_K=o(K)$; for example $k_j=\lceil j(\log(j+2))^2\rceil$. This also gives $\log A_b(\ell_{j(K)})=o(K)$, because $A_b(\ell_{j(K)})$ divides $\varphi(\Lambda_K)<\Lambda_K$. At $k=k_j$ let $\mu_k=\ell_j$, and let $u_k$ be the least positive integer with $u_k\equiv\ell_j\pmod{p^j}$ and $\gcd(u_k,b\ell_j)=1$. Otherwise $\mu_k=u_k=1$. Put

$$
 W_S=\sum_{k\ge1}\frac{u_k}{p^k\mu_k}\,b^{-p^k}.
$$

Then every prime $\ell\nmid b$ divides the shifted prefix denominators of $W_S$ from some point on. $P(W_S)$ is normal in base $b$ with $D_N\ll_PN^{-\eta_P}$ for **every** nonconstant $P\in\mathbb Q[x]$. And $\mu(W_S)=p$.

*Proof.* The all-prime property is as in Theorem G(1). The irrationality exponent is Theorem G(3) with $\lambda=p\ge3$, $D_k=p^k\Lambda_k$, and $c_k\le p^{j-k_j}\operatorname{rad}(b)\le\operatorname{rad}(b)$.

*Pole retention for all degrees.* Without auxiliary primes, $W_S$ is the Stoneham number $\alpha_{b,p}$. Its "full denominator growth" ([Phase 14](../phase14/quantitative-composites.md#arithmetic-at-every-insertion), resting on the periodic-mass theorem of Phase 13 for $c=p>2$) gives, for each $Y$ of degree $d$, a precision $l$ with $v_p(q_n)\ge dk-(l-1)-O_Y(1)$ on every late shell $p^k\le n<p^{k+1}$. That residue modulo $p^l$ involves only tuples whose reflected losses $k-j_i$ total at most $l-1$, since other tuples carry $p^{l}$. In $W_S$ such a tuple uses only indices $j_i\ge k-l+1$. Since the $k_j$ are strictly increasing, once $k\ge k_{l-1}+l$ every auxiliary index $k_J$ in that window has $J\ge l$. So its unit $u/\ell\equiv1\pmod{p^l}$, and $b^{-p^{j}}$ is unchanged. The residues modulo $p^l$ of $p^{dk}R_d$ for $W_S$ and $\alpha_{b,p}$ therefore coincide on late shells, and the pole retention transfers verbatim. Lower degrees $a<d$ have $p^{ak}R_a\in\mathbb Z_{(p)}$, because $\Lambda_k$ is prime to $p$. So in $p^{dk}R_Y$ they carry $p^{(d-a)k}$ and cannot cancel $A_dp^{dk}R_d$ once $k>l-1+v_p(A_d)$.

*Digits.* Insertions number $O((\log N)^d)$. For $d>p$ distinct tuples may share a position, but at most $(\log_pm+1)^d$ tuples sit at position $m$, which the buffer factor $b^{-\lceil2\log_bN\rceil}=N^{-2}$ absorbs. Run Theorem G's argument with $v\in[dk-O(1),dk+O(1)]$, $Q'\mid\Lambda_k^dD'_0$ and $\log\operatorname{ord}_{\Lambda_k^d}(b)\le(d-1)\log\Lambda_k+\log A_b=o(k)$. Here $\Lambda_k=N^{o(1)}$, so §2 gives $A(G)=O(\log\log N)$ directly. $\square$

In the script, for $p=3$, $b=2$ and auxiliary primes $5,7,11$ at indices $2,4,6$, the maximal depth defect $dk-v_3(q_n)$ over all insertion positions stays bounded. Shell by shell it is constant at 3, 4 and 8 for $d=2,3,4$, and for $d=5$ it is $8,10,10,10,12,10$ on $k=3,\ldots,8$ (for $\alpha_{2,3}$: $8,9,11,10,10,10$). On the last shell the modified number and $\alpha_{2,3}$ agree for every $d$. These auxiliary indices never lie in the active window with $J\ge l$, so the script also tests the congruence directly. With auxiliary primes $5,7,\ldots,29$ at $k_J=J+1$ ($J\le8$), $p^{dk}R_d(n)$ agrees with $\alpha_{2,3}$ modulo $3^l$ and is nonzero there. This holds at all 42 positions of shells $k=8,\ldots,11$ for $(d,l)=(2,4)$, and at all 121 positions of shells $k=10,11$ for $(d,l)=(3,5)$. The auxiliary indices inside the window are $5,\ldots,9$ for $d=2$ and $6,\ldots,9$ for $d=3$. Theorem S settles, for this kind of construction, the question left by Theorem U: all degrees, every off-radix prime, and a finite exponent can coexist. What is new relative to Phase 14 is the growing support, handled by Corollary B. The price is a fixed geometric schedule $b^{-p^k}$, in place of the quasi-polynomial one.

## 8. Obstacles to alternative constructions

1. **Base-$(r+1)$ weights.** With $e_k=B(r+1)^k$ all $r$-fold weight sums are distinct, and the script checks this for indices $\le12$, $r=2,3$. The leading pole is then never cancelled. But $q_n\approx p^{rB(r+1)^K}$ while runs have length $\lambda^K$, so the period is $b^{O((r+1)^K)}$. That is $o(b^{n_K})$, **not** $o(n_K)$. Already at $K=10$, $r=2$, one has $\log_2p^{re_K}\approx1.9\times10^5$ against $\log_2\lambda^K=20$. Runs are polylogarithmic in $q$: complete periods fail, and Lemma A, Vandehey and `SmoothOrbit` all need $T\ge q^\theta$. Linear weights with $p>(r+1)!$ (Theorem G) replace this.
2. **A new prime at every index.** For $W=\sum1/(p^k\ell_kb^{3^k})$ the complete-period bound $tp^kA(\ell_k)$ is not $o(3^k)$, already because $p^k\ge3^k$. Lemma A removes the $p$-part of that cost, but Corollary B still needs the auxiliary stride $\operatorname{lcm}_{j\le k}\operatorname{ord}_{\ell_j}b\le T^{1-\eta}$ with $T\asymp3^k$. For $b=2$ the script finds $\log\operatorname{lcm}_{j\le k}\operatorname{ord}_{\ell_j}2>k\log3$ for every $36<k\le3000$ (1565 against 1099 at $k=1000$). This is a finite computation: no lower bound for $\log A_b(\ell_k)$ is proved here, and the upper bound is only $\ll k\log\log k$ (§4). Theorem G therefore uses sparse primes, as in $(\mathrm P_G)$; the every-index version is neither covered nor disproved.
3. **$\lambda>r+1$ is not needed.** $\lambda>r$ already makes the windows $[ln_K,ln_K+(r-l)n_{K-1}]$ harmless, because the present set is a lexicographic initial segment. At the start of those windows the top multiset is $(K^{l-1},(K-1)^{r-l+1})$, not one containing $K^l$. So with linear weights the "protected pole" is not $p^{le_k}$ but $p^{w^*}$ with $w^*\ge r(K-1)$.
4. **Truncation separation for $n_{k+1}/n_k\to1$.** The exponent bound $\limsup n_{k+1}/(n_{k+1}-n_k)$ is the correct output of the method, and it is $+\infty$. Proposition 5.1 records the finite measure function that the method gives in that case.
5. **Earlier primes in Theorem H.** The budget is $(r-1)\log\Lambda_K+\log A_b<(1-\frac rd)\log N$, not $r\log\Lambda_K<(1-\frac rd)\log N$. For degree $\ge2$ the threshold $\log n_j\asymp j\log j$ is not improved in order of magnitude (§4).
6. **Dependence on $a_0(B)$.** It is linear: Lemma A needs $A(G)\le\frac3{16}\log_pM_0-1$, and the example in §1 shows that $A(G)\ge\log_pM+O(1)$ can kill all cancellation. In all applications here $A(G)=O(\log N/\log\log N)$ by Lemma D, and $A(G)=O(\log\log N)$ when $\Lambda=N^{O(1)}$, as in Theorem S.

## 9. Exact checks

`python -B scripts/phase22_short_orbits.py` runs in under 10 seconds and exits 0. It checks the following.

- **Lemma A.** LTE in 31840 cases. Exact equality of complete orbits with $1+p^A\mathbb Z/p^e$, and vanishing of their sums (41 cases). The stride van der Corput inequality and the differenced-phase identity $c(G^{m+hw}-G^m)\equiv c_hG^mp^{A+k+v_p(h)}$ with $p\nmid c_h$. The sharpness example. The $(\theta,n_\theta,\delta)$ table for the gap range.
- **Corollary B on Theorem H.** For $b=2$, $p=3$, $s=2$, $r=2$ and $d=3,4,5,6$, at 53 shifts of $W^2$ with auxiliary primes $7,19,73,37,5$: exact reduced denominators $q=3^eQ$ with $Q\mid\Lambda_K^2$; the identities $v_3(2^L-1)=v_3(2^{2T_Q}-1)=1+v_3(T_Q)$; agreement of the direct and CRT-split orbit sums of length 1500 to $10^{-8}T$ for frequencies $h=1,2,3$. The identity is also checked on all 243 divisors of $\prod\ell^2$.
- **Theorem G.** The lexicographic initial segment, the candidate formula, the bound $(r+1)!$ on the tied multiplicity, and the exact valuation $v_p(\text{prefix})=-w^*+v_p(A_r)$ at all 145 insertion positions for $(r,p,b,\lambda)=(1,3,2,3)$, $(2,7,2,3)$ and $(3,29,2,4)$, with polynomials $4x+1$, $5x^2+2x+3$ and $29x^3+3x^2+1$. The cancellation at $p=3$. Exact $\operatorname{den}U_k$, the exponent ratios, and the 724 convergents in the tested range.
- **Theorem S.** Bounded depth defects (at most 12) for $d=2,\ldots,5$, compared with $\alpha_{2,3}$. The exact congruence modulo $3^l$ with $\alpha_{2,3}$ at 42 and 121 positions, with auxiliary indices inside the active window.
- **Tables.** The ratios $\rho_k$ for Theorems H and U, and the cost of a prime at every index.

The finite computations check exact identities and illustrate the mechanisms. The asymptotic statements rest on the written proofs. Lemma A and Corollary B are elementary and self-contained. Lemma D and the sieve bound for $A(x)$ use only the divisor bound, the prime number theorem and the Selberg upper-bound sieve. Theorem S additionally uses the Phase 13/14 periodic pole retention.
