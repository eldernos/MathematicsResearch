# Rational scalings and signed special-function values

Phase 23, Track A, sub-tracks A3 and A4. Notation follows [`flagship-digit-laws.md`](../phase22/flagship-digit-laws.md) (cited as F22): $b\ge2$ is the radix, $f_w(N)$ the frequency of the word $w$ among the first $N$ shifts, $E_b=\prod_{k\ge1}(1-b^{-k})$, $D=q\,d/dq$, $\Theta_3(1/b)=1+2\sum_{k\ge1}b^{-k^2}$, $P(j)=j(3j-1)/2$ ($j\in\mathbb Z$) and $T_i=i(i+1)/2$. For a rational scaling $\tfrac adz$ we always assume $\gcd(d,b)=1$, $\gcd(a,d)=1$, $a\ne0$, and write $t=\operatorname{ord}_d(b)$, $q=b^{-1}\bmod d$. When $t$ is even put $h=t/2$, $\iota=b^h\bmod d$ (an involution, $\iota\ne1$) and $d_-=\gcd(d,\iota+1)$, the largest divisor of $d$ on which $\iota\equiv-1$; then $d_->1$, and $d_+=d/d_-$ divides $\iota-1$ (because $d\mid(\iota-1)(\iota+1)$). For odd $d$, moreover, $\gcd(d_+,d_-)=1$ and $d_+=\gcd(d,\iota-1)=d/d_-$, so $\mathbb Z/d\cong\mathbb Z/d_+\times\mathbb Z/d_-$ by CRT. For even $d$ this splitting can fail: $d=8$, $b=3$ gives $\iota=3$, $d_-=4$, $d_+=2$ and $\gcd(d_+,d_-)=2$. §§2–3 use the splitting only for odd $d$. All frequencies of rational scalings are statements **in the construction radix $b$** of the scaled series.

## Summary

| Result | Status |
| --- | --- |
| Theorem 0.1: signed-automaton digit laws extend to $\tfrac adD^jE_b$, $\tfrac adD^jE_b^3$ ($j\ge0$) and $\tfrac ad\Theta_3(1/b)$, in base $b$ | Paper proof (F22 Theorem 5.2 argument) |
| Lemma 0.2: exact limit discrepancy $D_\infty$ of a split atomic law | Paper proof |
| **Theorem 1.1 (reflection symmetry):** for every $d$ coprime to $b$, the nonzero atoms of all these laws are symmetric under $c\mapsto-c$; hence $f_w=f_{\bar w}$ for every non-constant $w$, $f_{0^L}-f_{(b-1)^L}=\operatorname{sgn}(a)(w_0^+-w_0^-)$, and in base 2 $f_0=\tfrac12+\operatorname{sgn}(a)(w_0^+-w_0^-)/2$. The "$-1\in\langle2\rangle$" dichotomy plays no role | Paper proof; exact check for every law computed (odd $d\le200$ in base 2; all $d\le100$ in bases 3–10; $D^jE_b$, $j=1,2$, for 8 even $d$ with $b$ odd) |
| Lemma 2.1: for odd $d$ the head sums of $E_b$ and $E_b^3$ have vanishing period sums; $A(k+t)=\iota A(k)$, $V(k+L)=\iota V(k)$ | Paper proof; checked |
| **Theorem 2.2–2.3 (parity formula):** $f_0(\tfrac adE_2)=\tfrac12+\operatorname{sgn}(a)\,\Xi(d)/(6t)$ and $f_0(\tfrac adE_2^3)=\tfrac12+\operatorname{sgn}(a)\,\Xi_3(d)/(2L)$ with explicit integers $\Xi,\Xi_3$; $\Xi$ is odd unless the half-period head sum vanishes mod $d_-$ | Paper proof; formula checked for all 16,300 + 16,300 base-2 laws with odd $d\le200$ |
| **Theorem 3.2 + Corollary 3.3:** Conjecture 5.5 of F22 holds for every odd $d\le20000$ ($E_2$) and every odd $d\le3000$ ($E_2^3$), and more generally whenever $d_-$ has a prime factor below these bounds | Paper proof + exact finite computation (no exceptional prime below the bounds) |
| **Example 3.4:** $(a/113)E_{10}$ has even order $t=112$ and a complement-symmetric limit law: the radix-free converse of F22 Theorem 5.3 is false | Paper proof (exact law) |
| Conjecture 5.5 for all odd $d$ | **Open**; reduced to "balanced exceptional primes"; heuristically expected to fail at some very large prime (§3.5) |
| No rational scaling of $E_b$ or $E_b^3$ is simply normal in base $b\in\{3,\dots,10\}$ among 42,296 laws | Finite computation of exact laws; general $b\ge3$ **Open** |
| **Theorem 5.2:** $\tfrac ad\Theta_3(1/2)$ is simply normal in base 2 for every odd $d$ divisible by 3; exact criterion and list (48 values of $d\le200$) | Paper proof; list from exact laws |
| **Theorem 5.3:** $\tfrac ap\Theta_3(1/b)$ is simply normal in its construction radix $b$ when $\operatorname{ord}_p(b)=p-1\equiv2\pmod4$, $b\mid p-1$ and the theta head sums avoid $0\bmod p$. Example: $\tfrac17\Theta_3(1/3)$ in base 3 | Paper proof; 30 pairs $(b,p)$ checked |
| Theorem 5.1(i): odd $\operatorname{ord}_d(2)$ forces a zero atom, so $\tfrac ad\Theta_3(1/2)$ is then **not** simply normal in base 2 | Paper proof |
| Theorem 6.1: $\tfrac adD^jE_b$, $\tfrac adD^jE_b^3$ have complement-symmetric laws when $d$ and $\operatorname{ord}_d(b)$ are odd; in base 2 simply normal. The content of $D^jE^3$ is exactly 3 for every $j\ge1$; Corollary 6.2 transfers Theorem 6.1 to the reduced denominator $d/3$ for odd $d$ with $3\parallel d$ | Paper proof; base-2 lists for $d\le45$ |
| Theorem 7.1: $\tfrac a2E_b^2$ in odd base $b$: $f_{((b-1)/2)^L}\to\tfrac23$, $f_{0^L}+f_{(b-1)^L}\to\tfrac13$, all other words $\to0$; not simply normal in base $b$ | Paper proof; the split of $\tfrac13$ is **Open** |
| **Theorem 8.1:** $\tau_{r,M}-\tau_{M-r,M}\ge0$ for all $n$ iff $r\mid M$ and $M/r\in\{3,4,6,8,12,24\}$; otherwise negative values recur ($a(nq)=2a(n)$) | Paper proof; 59 nonnegative and 811 signed pairs for $M\le60$, each signed pair with a witness |
| **Theorem 9.2 (universal sign flip):** $a_{r,M'}(nm)=-a_{r,M'}(n)$ for some $m$ and all $n$ prime to $m$ **iff** $-1$ is a square mod $M'$; then $m=q_1^2q_2^2$ | Paper proof; 52,870 triples checked |
| Theorem 9.4–9.5: every complex character admits $(1*\chi)(m)=-1$; dominant-part flips for all cyclic moduli | Paper proof; 32,344 triples checked |
| **Theorem 10.1–10.2:** both signs of $a_{r,M}$ have positive lower density relative to the support when $(\mathbb Z/M')^\times$ is cyclic with $\varphi(M')\ge4$, and in the real type | Paper proof with cited Wirsing theorem |
| Theorem 10.3: then $\liminf f_{0^L}>0$ and $\liminf f_{(b-1)^L}>0$ in every base $b$ | **Conditional** on a pair-sieve bound (S$_U$) |
| §11: the conjugation $\chi\mapsto\bar\chi$ on $\operatorname{Im}(1*\chi)$ carries no information about a single number; the arithmetic flip $n\mapsto196n$ does | Paper proof; base-2 simple normality and exact bias **Open** |

Everything finite comes from [`scripts/phase23_rational_signed.py`](../../scripts/phase23_rational_signed.py) (§13), which uses exact `int`/`Fraction` arithmetic. Finite digit statistics are labelled *finite measurement* and are not evidence for limits. No Lean declaration is claimed; §12 lists recommended finite cores.

## 0. Setup

### 0.1 Three families and their head sums

Write each series as $z=\sum_mc(m)b^{-m}$, with integral head $I_n=\sum_{m\le n}c(m)b^{n-m}$. Then $b^n\tfrac adz=\tfrac adI_n+\tfrac ad\tau_n$, and the atom at shift $n$ is $aI_n\bmod d$ (F22 §5). At the insertion points the head residues are:

- **Euler type**, $z=D^jE_b$ ($j\ge0$): insertions at $P(i)$, $i\in\mathbb Z$, coefficient $(-1)^iP(i)^j$. With $\mathrm{tm}(i)=(-1)^iP(i)^jq^{P(i)}\bmod d$,

  ```math
  u_k^-=b^{P(k)}A^-(k),\quad A^-(k)=\sum_{i=1-k}^{k}\mathrm{tm}(i);\qquad u_k^+=b^{P(-k)}A(k),\quad A(k)=\sum_{i=-k}^{k}\mathrm{tm}(i).
  ```

  The run after $P(k)$ has length $k$, sign $(-1)^k$ and weight class $\tfrac13$. The run after $P(-k)$ has length $2k+1$, sign $(-1)^{k+1}$ and weight class $\tfrac23$ (F22 Theorem 5.2).
- **Cube type**, $z=D^jE_b^3$: insertions at $T_i$, coefficient $(-1)^i(2i+1)T_i^j$. With $\mathrm{tm}_3(i)=(-1)^i(2i+1)T_i^jq^{T_i}$, the head after $T_k$ is $v_k=b^{T_k}V(k)$ with $V(k)=\sum_{i=0}^k\mathrm{tm}_3(i)$. The run has length $k+1$ and sign $(-1)^{k+1}$, and all classes have equal weight.
- **Theta**, $z=\Theta_3(1/b)$: insertions at $k^2$, coefficient 2 (and 1 at 0). The head after $k^2$ is $b^{k^2}B(k)$ with $B(k)=\sum_{|i|\le k}q^{i^2}$. The run has length $2k+1$, every sign is $+1$, and all classes have equal weight.

The term sequences are periodic in $i$, with period $\Lambda$: $2t$ for $E_b$; $t$ for $\Theta_3$; $2\operatorname{lcm}(t,d)$ for $D^jE_b$ with $j\ge1$; $2\operatorname{lcm}(t,d)$ for the cube type. (For even $\Lambda$, $P(i+\Lambda)-P(i)=\frac\Lambda2(6i+3\Lambda-1)$ has 2-adic valuation $v_2(\Lambda)-1$, so $2d\mid\Lambda$ guarantees that $P(i)^j$ is $\Lambda$-periodic mod $d$ for every $j\ge1$, and is necessary for $j=1$. The smaller value $\operatorname{lcm}(2t,d)$ is therefore not a period when $d$ is even with $v_2(d)>v_2(t)$ and $j=1$. For $DE_3$ mod 2, $P(0)=0\not\equiv P(2)=5$. The script checks $2\operatorname{lcm}(t,d)$ and the failure of $\operatorname{lcm}(2t,d)$ on 8 such pairs $(b,d)$. For odd $d$ the two values coincide.) Over one block the head sums drift by a fixed amount: $2\sigma$ (Euler and theta) or $\sigma$ (cube), where $\sigma$ is the sum over one period. Put $g=\gcd(2\sigma,d)$ (respectively $\gcd(\sigma,d)$). A class $k$ then spreads its weight uniformly over the coset $\mathrm{head}(k)+g\mathbb Z/d$, and each run spreads it uniformly over the $\times b$ orbit. The zero atom receives mass $g/d$ from each class whose head is $\equiv0\pmod g$, split by the run sign into $w_0^+$ (word $0^L$ when $a>0$) and $w_0^-$ (word $(b-1)^L$).

**Theorem 0.1 (signed automaton, extended).** For each family and each $L$, the length-$L$ word frequencies of $\tfrac adz$ in base $b$ converge to the rational limits given by the formula of F22 Theorem 5.2 with the head sums above. The error is $O(1/\sqrt N)$ for $E_b$ and $\Theta_3$, and $O(\log N/\sqrt N)$ otherwise.

*Proof.* F22's proof of Theorem 5.2 uses only three inputs: (i) the remainder after each insertion is eventually $\le\frac12$, which holds by F22 Lemma 2.1 for the derivative families and trivially for $\Theta_3$; (ii) an exceptional window of length $L+\lceil\log_b(|a|(|c|+\frac12))\rceil+1=O(L+\log N)$ before each insertion; (iii) run lengths that are the same linear function of $k$ in every residue class of $k$. The coset spreading is exact, because the class $k+m\Lambda$ has head $\mathrm{head}(k)+m\cdot(\text{drift})$. $\square$

### 0.2 Limit discrepancy

**Lemma 0.2.** Let the limit law put mass $m_c$ on the atom $c/d$ for $1\le c\le d-1$, mass $m_0=w_0^+$ at $0^+$ and mass $m_d=w_0^-$ at $1^-$. Then $D_N\to D_\infty=\max(D^+,D^-)$, where

```math
D^+=\max_{0\le i\le j\le d}\Bigl(\sum_{c=i}^{j}m_c-\frac{j-i}d\Bigr),\qquad D^-=\frac1d+\max\Bigl(0,\ \max_{1\le i\le j\le d-1}\sum_{c=i}^{j}\Bigl(\frac1d-m_c\Bigr)\Bigr).
```

*Proof.* Outside $o(N)$ shifts, every point $x_n$ lies within $o(1)$ of its atom, and atom 0 is approached from the side given by its sign. A half-open interval $[x,y)$ with $x$ just below $i/d$ and $y$ just above $j/d$ captures the closed atom range $[i/d,j/d]$. One with $x$ just above $i/d$ and $y$ just below $j/d$ captures the open range. Every interval is sandwiched between such extremal ones, and finitely many atoms make the convergence uniform. $\square$

## 1. The reflection symmetry

**Theorem 1.1.** Let $z$ be $D^jE_b$, $D^jE_b^3$ ($j\ge0$) or $\Theta_3(1/b)$, let $d\ge2$ be coprime to $b$, and let $a\ne0$ be coprime to $d$. The limit law of the nonzero atoms of $\tfrac adz$ is invariant under $c\mapsto-c$. Consequently, for every $L$, in base $b$:

1. $f_w=f_{\bar w}$ for every word $w\notin\{0^L,(b-1)^L\}$, where $\bar w_i=b-1-w_i$;
2. $f_{0^L}-f_{(b-1)^L}=\operatorname{sgn}(a)\,(w_0^+-w_0^-)$;
3. in base 2, $f_0(\tfrac adz)=\tfrac12+\operatorname{sgn}(a)(w_0^+-w_0^-)/2$. For $\Theta_3$, where all signs are $+$, this reads $f_0=\tfrac12+\operatorname{sgn}(a)w_0/2$.

So $\tfrac adz$ is simply normal in base 2 **iff its zero split is balanced** (for $\Theta_3$: iff it has no zero atom). The complement symmetry of the full word law holds iff $w_0^+=w_0^-$.

*Proof.* Let $S:\mathbb Z\to\mathbb Z/d$ satisfy $S(0)=0$ and $S(n+1)-S(n)=\mathrm{tm}(n)$. Then $A^-(k)=S(k+1)-S(1-k)$ and $A(k)=S(k+1)-S(-k)$ for every $k\in\mathbb Z$. On this extension the residue sequences are periodic with the period $P$ of the automaton, so classes indexed by negative $k$ are classes modulo $P$. Hence

```math
A^-(-k)=-A^-(k),\qquad A(-k)=-A(k-1),
```

and with $P(-k)-P(k)=k$ and $P(k)-P(1-k)=2k-1$,

```math
u^-_{-k}=-b^{k}\,u^-_k,\qquad u^+_{-k}=-b^{2k-1}\,u^+_{k-1}.
```

The involutions $k\mapsto-k$ (on "$-$" runs) and $k\mapsto-1-k$ (on "$+$" runs) of $\mathbb Z/P$ preserve the class weights $\frac13,\frac23$. They send each orbit, and each coset $\mathrm{head}+g\mathbb Z/d$, to its negative. For the cube type, $T_{-1-i}=T_i$ and $2(-1-i)+1=-(2i+1)$ give $\mathrm{tm}_3(-1-i)=\mathrm{tm}_3(i)$. Hence $S_3(-n)=-S_3(n)$, $V(-2-k)=-V(k)$ and $v_{-2-k}=-b^{k+1}v_k$. For $\Theta_3$, $q^{i^2}$ is even in $i$, so $B(-1-k)=-B(k)$. This proves the symmetry. The expansion of $(d-c)/d$ is the digitwise complement of that of $c/d$, and nonzero atoms are interior (F22 Lemma 5.1). So nonzero atoms contribute complementary words with equal mass, and only the zero atom breaks the symmetry. $\square$

*Remark.* The orbit of a nonzero atom is closed under negation iff $-1\in\langle b\rangle$ modulo the relevant divisor. Theorem 1.1 does not use this: the symmetry pairs **different** classes $k\leftrightarrow-k$. For example $d=21$ ($-1\notin\langle2\rangle$) and $d=3$ ($-1\in\langle2\rangle$) behave identically, with $f_0(\tfrac1{21}E_2)=\tfrac{19}{36}$ and $f_0(\tfrac13E_2)=\tfrac7{12}$, and in both cases $f_0-\frac12$ is exactly half the zero-split imbalance.

## 2. Vanishing period sums and the parity formula

**Lemma 2.1.** Let $d$ be odd and coprime to $b$.

1. (Euler, $j=0$) $\sum_{i=0}^{2t-1}\mathrm{tm}(i)\equiv0$, so $g=d$. If $t$ is even, then $\mathrm{tm}(i+t)=\iota\,\mathrm{tm}(i)$, $A(k+t)=\iota A(k)$ and $A^-(k+t)=\iota A^-(k)$.
2. (Cube, $j=0$) With $L=\operatorname{lcm}(t,d)$, $\sum_{i=0}^{L-1}\mathrm{tm}_3(i)\equiv0$, so $g=d$. If $t$ is even, then $V(k+L)=\iota V(k)$.

*Proof.* (1) We have $P(i+t)-P(i)=t(6i+3t-1)/2$. For $t$ odd this is $\equiv0\pmod t$ and the sign flips, so $\mathrm{tm}(i+t)=-\mathrm{tm}(i)$ (F22 Theorem 5.3). For $t$ even it is $\equiv h\cdot\text{odd}\pmod t$, so $\mathrm{tm}(i+t)=\iota\,\mathrm{tm}(i)$. We prove "every sum of $2t$ consecutive terms vanishes mod $d$" by induction on $d$. If $t$ is odd or $\iota\equiv-1$, the sequence is antiperiodic and the claim holds. Otherwise $d=d_+d_-$ with both factors $>1$. Modulo $d_-$ the sequence is antiperiodic with antiperiod $t$. Modulo $d_+$ one has $b^h\equiv1$, so $t_+=\operatorname{ord}_{d_+}(b)$ divides $h$, and $2t$ is a multiple of $2t_+$. The term sequence mod $d_+$ is the one attached to $d_+$, and $d_+<d$, so the induction hypothesis applies. Then $A(k+t)=\sum_{i=-k}^k\mathrm{tm}(i-t)+(\text{$2t$ consecutive terms})=\iota A(k)$, and likewise for $A^-$.

(2) For $t$ odd, $L$ is odd, $\mathrm{tm}_3(i+L)=-\mathrm{tm}_3(i)$, and the involution $i\mapsto L-1-i$ gives $\sum_{i<L}\mathrm{tm}_3=0$ (F22 Theorem 5.3). For $t$ even, $L$ is even with $v_2(L)=v_2(t)$, $T_{i+L}-T_i=\frac L2(2i+L+1)\equiv h\cdot\text{odd}\pmod t$, and $2L\equiv0\pmod d$. Hence $\mathrm{tm}_3(i+L)=\iota\,\mathrm{tm}_3(i)$, and so $\mathrm{tm}_3(L-1-i)=\iota\,\mathrm{tm}_3(-1-i)=\iota\,\mathrm{tm}_3(i)$. Summing over $i<L$ gives $(1-\iota)\sigma_L=0$, so $\sigma_L\equiv0\pmod{d_-}$. Modulo $d_+$, $L$ is a multiple of $2\operatorname{lcm}(t_+,d_+)$, because $v_2(t_+)<v_2(t)$. Induction gives $\sigma_L\equiv0\pmod{d_+}$. Finally $V(k+L)=\sigma_L+\iota V(k)$. $\square$

**Theorem 2.2 (parity formula, Euler).** Let $d$ be odd with $t$ even, and put $z_k=[A^-(k)\equiv0\pmod d]$. Then, in base $b$,

```math
w_0^+-w_0^-=\frac{\Xi_b(d)}{3t},\qquad \Xi_b(d)=\sum_{k=1}^{t}(-1)^kz_k=1+(-1)^hz_h+2\sum_{k=1}^{h-1}(-1)^kz_k,
```

and $z_h=[A^-(h)\equiv0\pmod{d_-}]$. Here $w_0^\pm$ are defined by the run sign alone (§0.1), so by Theorem 1.1 $f_{0^L}-f_{(b-1)^L}=\operatorname{sgn}(a)\,\Xi_b(d)/(3t)$. In particular $\Xi_b(d)$ is **odd**, so the split is unbalanced, whenever $A^-(h)\not\equiv0\pmod{d_-}$ (the *half-period test*). In base 2,

```math
f_0\bigl(\tfrac adE_2\bigr)=\frac12+\operatorname{sgn}(a)\,\frac{\Xi_2(d)}{6t}\qquad\text{exactly}.
```

*Proof.* By Lemma 2.1, $g=d$ and the period is $2t$. On "$+$" runs the zero set is invariant under $k\mapsto-1-k$ (Theorem 1.1), which reverses the sign $(-1)^{k+1}$ and has no fixed point modulo $2t$; these runs contribute 0. On "$-$" runs $z_{-k}=z_k$ with equal signs. The fixed points of $k\mapsto-k$ modulo $2t$ are $0$ and $t$, and $z_0=1$ (since $A^-(0)=0$) and $z_t=1$ (since $A^-(t)=\iota A^-(0)$), both with sign $+$. Summed over $\mathbb Z/2t$ with weight $1/(6t)$, this gives $(2+2\sum_{0<k<t}(-1)^kz_k)/(6t)=\Xi/(3t)$. Since $A^-(t-k)=\iota A^-(-k)=-\iota A^-(k)$, $z_{t-k}=z_k$, which yields the second expression for $\Xi$. Finally $A^-(-h)=-A^-(h)$ and $A^-(-h)=A^-(h-t)=\iota A^-(h)$, so $(1+\iota)A^-(h)=0$, i.e. $A^-(h)\equiv0\pmod{d_+}$ automatically. $\square$

**Theorem 2.3 (parity formula, cube).** Let $d$ be odd, $t$ even, $L=\operatorname{lcm}(t,d)$, and $y_k=[V(k)\equiv0\pmod d]$. Then

```math
w_0^+-w_0^-=\frac{\Xi_3(d)}{L},\qquad \Xi_3(d)=\sum_{k=0}^{L-1}(-1)^{k+1}y_k=1+(-1)^{L/2}y_{L/2-1}+2\sum_{\text{pairs}}(\pm y_k),
```

where the pairs are the orbits of $k\mapsto-2-k$ on $\mathbb Z/L$ off its two fixed points $-1$ and $L/2-1$. Also $y_{L/2-1}=[V(L/2-1)\equiv0\pmod{d_-}]$. So $\Xi_3$ is odd whenever $V(L/2-1)\not\equiv0\pmod{d_-}$. By Theorem 1.1, $f_{0^L}-f_{(b-1)^L}=\operatorname{sgn}(a)\,\Xi_3(d)/L$ and $f_0(\tfrac adE_2^3)=\tfrac12+\operatorname{sgn}(a)\Xi_3(d)/(2L)$.

*Proof.* Same as Theorem 2.2, using the involution $k\mapsto-2-k$, which preserves the sign $(-1)^{k+1}$. It has fixed points $k\equiv-1$ (where $V(-1)=0$) and $k\equiv L-1$ (where $V(L-1)=\sigma_L=0$) modulo $2L$, and $L$-periodicity of the zero set by Lemma 2.1. $\square$

*Exact values* (all laws from the script; $\Xi$ for $E_2$, $\Xi_3$ for $E_2^3$, $a>0$):

| series | $d$ | $t$ or $L$ | $\Xi$ | $f_0$ |
| --- | --- | --- | --- | --- |
| $E_2$ | 3 | 2 | 1 | $7/12$ |
| $E_2$ | 5 | 4 | 1 | $13/24$ |
| $E_2$ | 13 | 12 | $-1$ | $35/72$ |
| $E_2$ | 21 | 6 | 1 | $19/36$ |
| $E_2$ | 37 | 36 | 1 | $109/216$ |
| $E_2$ | 67 | 66 | $-1$ | $197/396$ |
| $E_2^3$ | 3 | $L=6$ | 1 | $7/12$ |
| $E_2^3$ | 5 | $L=20$ | $-1$ | $19/40$ |
| $E_2^3$ | 35 | $L=420$ | $-3$ | $139/280$ |

Over all odd $d\le200$, $\max|\Xi|=9$ for $E_2$ and $\max|\Xi_3|=29$ for $E_2^3$. The values for $d=3,13$ ($E_2$) and $d=35$ ($E_2^3$) reproduce F22's zero splits $(\tfrac16,0)$, $(\tfrac1{36},\tfrac1{18})$ and $(\tfrac1{140},\tfrac1{70})$.

*Exact $D_\infty$* (Lemma 0.2, $a=1$): $\tfrac13E_2$: $\tfrac12$; $\tfrac15E_2$: $\tfrac{19}{60}$; $\tfrac17E_2$: $\tfrac{11}{63}$; $\tfrac1{13}E_2$: $\tfrac1{12}$; $\tfrac1{23}E_2$: $\tfrac1{11}$; $\tfrac13E_2^3$: $\tfrac12$; $\tfrac17E_2^3$: $\tfrac17$.

**Base-2 catalogue (exact, odd $d\le200$).** All 16,300 laws $\tfrac adE_2$ and all 16,300 laws $\tfrac adE_2^3$ were computed, one for each pair ($a\bmod d$, $\operatorname{sgn}a$). By $\times2$-invariance it suffices to take one $a$ per coset of $\langle2\rangle$. Simple normality in base 2 holds exactly for the 16 odd-order denominators $d\in\{7,23,31,47,49,71,73,79,89,103,127,151,161,167,191,199\}$, for both series and every $a$. Every even-order $d\le200$ passes the half-period test. This extends F22's range $d<64$ (resp. $d<46$).

## 3. Prime reduction and the status of Conjecture 5.5

**Definition.** Let $p\nmid 2b$ be prime with $t_p=\operatorname{ord}_p(b)$ even. Then $p$ is *$b$-exceptional* if $A^-_p(t_p/2)\equiv0\pmod p$, and *cube-$b$-exceptional* if $V_p(pt_p/2-1)\equiv0\pmod p$. Here the subscript $p$ means the head sums attached to the denominator $p$.

**Lemma 3.1.** Let $p\mid d_-$. Then $t_p$ is even and $t/t_p$ is odd, and

```math
A^-(h)\equiv\pm A^-_p(t_p/2)\pmod p,\qquad V(L/2-1)\equiv\pm V_p(L_p/2-1)\pmod p\quad(L_p=pt_p,\ L/L_p\ \text{odd}).
```

*Proof.* $b^h\equiv-1\pmod p$ forces $t_p\mid 2h$ and $t_p\nmid h$. Modulo the prime $p$, $b^{t_p/2}\equiv-1$, so $A^-(k+t_p)\equiv-A^-(k)$ by Lemma 2.1 applied to $p$. Write $h=t_p/2+t_p(m'-1)/2$ with $m'$ odd. For the cube, $v_2(L)=v_2(t)=v_2(t_p)=v_2(L_p)$, and $V(k+L_p)\equiv-V(k)\pmod p$. $\square$

**Theorem 3.2.** If $d_-$ has a prime factor that is not $b$-exceptional, then $\tfrac adE_b$ has an unbalanced zero split. If $d_-$ has a prime factor that is not cube-$b$-exceptional, so does $\tfrac adE_b^3$. In base 2, such a number is not simply normal.

*Proof.* Lemma 3.1 and Theorems 2.2–2.3: $z_h=0$ (resp. $y_{L/2-1}=0$), so $\Xi$ (resp. $\Xi_3$) is odd. $\square$

**Corollary 3.3 (Conjecture 5.5 up to explicit bounds).** No prime $p\le20000$ is 2-exceptional (1,615 primes with $\operatorname{ord}_p(2)$ even), and no prime $p\le3000$ is cube-2-exceptional (303 primes). Hence, for every odd $d$ such that $d_-$ has a prime factor $\le20000$ (resp. $\le3000$), and in particular for **every odd $d\le20000$** (resp. $\le3000$):

> $\tfrac adE_2$ (resp. $\tfrac adE_2^3$) is simply normal in base 2 $\iff$ $\operatorname{ord}_d(2)$ is odd,

for every numerator $a$ coprime to $d$. "If" is F22 Theorem 5.3. "Only if" is Theorem 3.2 together with the finite search. The prime reduction itself was checked on all 93 pairs $(d,p\mid d_-)$ with odd $d\le200$.

**Example 3.4 (the converse fails in base 10).** Among primes $p\le1000$, the only 10-exceptional one is $p=113$, and its zero split balances: for $\tfrac a{113}E_{10}$, $t=112$ is even and $w_0^+=w_0^-=\tfrac1{56}$. By Theorem 1.1 the limit word law is complement-symmetric for every $a$ (the script checks $L=1,2$ and $a\in\{1,3,-1\}$). Its digit law in base 10 is

```math
(f_0,\dots,f_9)=\Bigl(\tfrac{353}{3136},\tfrac{297}{3136},\tfrac{297}{3136},\tfrac{81}{784},\tfrac{297}{3136},\tfrac{297}{3136},\tfrac{81}{784},\tfrac{297}{3136},\tfrac{297}{3136},\tfrac{353}{3136}\Bigr),
```

so it is not simply normal in base 10. Complement symmetry with **even** order shows that "complement-symmetric $\iff$ odd order" is false as a radix-free statement. In base 2, complement symmetry is the same as simple normality (Theorem 1.1), so a 2-exceptional prime with balanced split would be a counterexample to Conjecture 5.5.

**Example 3.5.** In base 3, $p=5$ is cube-exceptional (the only one $\le300$), but the split of $\tfrac a5E_3^3$ is $(\tfrac3{10},\tfrac1{10})$, so exceptional primes need not balance. The digit law is $(\tfrac9{20},\tfrac3{10},\tfrac14)$ for $a>0$, and $(\tfrac14,\tfrac3{10},\tfrac9{20})$ for $a<0$.

**3.5 Heuristic and status.** Model $A^-_p(t_p/2)$ as uniform in $\mathbb Z/p$. Then the expected number of 2-exceptional primes up to $X$ grows like $c\log\log X\to\infty$, and an exceptional prime balances with positive conditional probability in both residue classes of $t_p$ modulo 4. If $t_p\equiv2\pmod4$, then $h$ is odd and $1+(-1)^hz_h=0$ already cancels the two fixed points, so balance needs only $\sum_{0<k<h}(-1)^kz_k=0$. If $t_p\equiv0\pmod4$, then $1+(-1)^hz_h=2$, and balance needs odd-indexed zeros to cancel it. Base 10 realizes the second case at $p=113$: $t_{113}=112\equiv0\pmod4$, the zeros of $A^-(k)$ mod 113 for $1\le k\le112$ are $k\in\{29,56,83,112\}$, and the odd pair $\{29,83\}$ cancels the even zeros $\{56,112\}$, so $\Xi_{10}(113)=0$ (script, R2). **We therefore expect Conjecture 5.5 to be false, with the first counterexample a prime far beyond $20000$.** This is a heuristic, not a theorem. Status: **Open**. A counterexample $d$ must have every prime factor of $d_-$ 2-exceptional (Theorem 3.2), hence $>20000$. Conversely, a balanced 2-exceptional prime $p$ is a counterexample $d=p$.

## 4. Other radices

By Theorem 1.1, $\tfrac adE_b$ or $\tfrac adE_b^3$ is simply normal in base $b\ge3$ iff the split is balanced and each cylinder $[e/b,(e+1)/b)$, $1\le e\le b-2$, carries nonzero-atom mass $1/b$; then $f_0=f_{b-1}=1/b$ automatically. The parity formula was checked in bases 3, 5 and 10 for all odd $d<121$. Among the 42,296 exact laws with $b\in\{3,\dots,10\}$ ($E_b$: $d\le100$; $E_b^3$: $d\le50$; every $a$, both signs), **none is simply normal in base $b$**. Structurally, for odd $d$, $E_b$ and $E_b^3$ always have a zero atom: the classes $k\equiv0,t$ (resp. $k\equiv-1,L-1$) have zero head, so $w_0\ge1/(3t)$ (resp. $\ge1/L$). Whether any rational scaling of $E_b$ or $E_b^3$ is simply normal in a base $b\ge3$ remains **Open**. The theta family in §5 has no forced zero atom, and there the answer is yes.

## 5. Rational scalings of $\Theta_3(1/b)$

Let $G=\sum_{i=0}^{t-1}q^{i^2}\bmod d$ and $g=\gcd(2G,d)$.

**Theorem 5.1.** For $\tfrac ad\Theta_3(1/b)$ in base $b$, the zero atom has mass $w_0=\frac gd\cdot\frac1t\#\{1\le k\le t:B(k)\equiv0\pmod g\}$, read as $0^L$ if $a>0$ and $(b-1)^L$ if $a<0$.

1. If $d$ is odd and $t$ is odd, then $w_0>0$.
2. If $g=1$, then $w_0=1/d$.
3. In base 2, $f_0=\tfrac12+\operatorname{sgn}(a)w_0/2$. So $\tfrac ad\Theta_3(1/2)$ is simply normal in base 2 iff $g>1$ and $B(k)\not\equiv0\pmod g$ for all $k$.

In particular **odd $\operatorname{ord}_d(2)$ is an obstruction** for $\Theta_3$, the reverse of the situation for $E_2$.

*Proof.* The mass formula is the coset description of §0.1 with constant sign $+$. Modulo $g$, $B$ has period $t$, and $B(-1-k)=-B(k)$. For $t$ odd, $k_0=(t-1)/2$ is a fixed point of $k\mapsto-1-k$, so $2B(k_0)\equiv0$ and $B(k_0)\equiv0\pmod g$. For $g=1$ every class contributes $1/d$. Part 3 is Theorem 1.1. $\square$

**Theorem 5.2 (the mod-3 theorem).** If $d$ is odd and $3\mid d$, then $\tfrac ad\Theta_3(1/2)$ is simply normal in base 2 for every $a$ coprime to $d$.

*Proof.* $\operatorname{ord}_3(2)=2$ divides $t$, so $t$ is even. Modulo 3, $q\equiv-1$, so $q^{i^2}\equiv(-1)^i$, and $G\equiv\sum_{i<t}(-1)^i=0$. So $3\mid g$. Also $B(k)\equiv1+2\sum_{i=1}^k(-1)^i\in\{1,-1\}\pmod 3$, so $B(k)\not\equiv0\pmod g$ and $w_0=0$. $\square$

**Base-2 list.** Exactly 48 odd $d\le200$ give simply normal $\tfrac ad\Theta_3(1/2)$ (for all $a$): all 33 odd multiples of 3, together with $d\in\{11,19,43,55,59,77,95,107,121,133,139,143,163,179,187\}$. Every prime $p\equiv3\pmod8$ has $\operatorname{ord}_p(2)\equiv2\pmod4$. Among the primes $p\equiv3\pmod8$ below 200, namely $3,11,19,43,59,67,83,107,131,139,163,179$, those giving simple normality are $3,11,19,43,59,107,139,163,179$. For $67,83,131$ some partial theta sum vanishes mod $p$.

**Theorem 5.3 (prime criterion, any radix).** Let $p\nmid b$ be an odd prime with $t=\operatorname{ord}_p(b)\equiv2\pmod4$, and suppose $B(k)\not\equiv0\pmod p$ for all $k$. Then $w_0=0$, and $\tfrac ap\Theta_3(1/2)$ is simply normal in base 2 when $b=2$. If moreover $b$ is a primitive root mod $p$ (so $p\equiv3\pmod4$) and $b\mid p-1$, then $\tfrac ap\Theta_3(1/b)$ **is simply normal in its construction radix $b$**, for every $a$ coprime to $p$.

*Proof.* Put $h=t/2$, which is odd. Then $q^{(i+h)^2}=q^{i^2}(q^h)^{2i+h}=-q^{i^2}$, so $G\equiv0$, $g=p$ and $w_0=0$. When $b$ is a primitive root, every nonzero head is a unit whose orbit is all of $(\mathbb Z/p)^\times$, so the atom law is uniform on the units. For $p=bm+1$, each interval $[ep/b,(e+1)p/b)$ contains exactly $m$ of the integers $1,\dots,p-1$. $\square$

*Examples.* $\tfrac17\Theta_3(1/3)$ is simply normal in base 3: each digit has frequency $\tfrac13$, the six words $01,02,10,12,20,21$ each have frequency $\tfrac16$, the words $00,11,22$ are absent, and $D_\infty=\tfrac27$. By contrast, $\Theta_3(1/3)$ itself has $f_0\to1$ in base 3 (F22 Theorem 1). For $d\le80$, the scalings that are simply normal in base $b$ are: $b=3$: $d\in\{7,14,19,31,35,38,43,49,62,70,74,77,79\}$; $b=6$: $d=79$; $b=7$: $d=71$; none for $b\in\{4,5,10\}$. The criterion of Theorem 5.3 was confirmed on 30 pairs $(b,p)$ with $b\in\{2,3,6,7\}$ and $p\le300$, and for $b=2$ the base-2 version ("$t\equiv2\pmod4$ and zero-free" $\iff$ simply normal) holds for every prime $p\le300$. This partly answers F22 Open problem 4: a rational scaling of a flagship value **can** be simply normal in a base $b\ge3$. The question for $E_b$ and $E_b^3$ stays open (§4).

*Exact laws in base 2* ($a=1$):

| $d$ | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $f_0$ | $1/2$ | $3/5$ | $4/7$ | $1/2$ | $1/2$ | $7/13$ | $1/2$ |
| $f_{00}$ | 0 | $2/5$ | $2/7$ | $1/3$ | $1/5$ | $4/13$ | $1/5$ |
| $f_{01}$ | $1/2$ | $1/5$ | $2/7$ | $1/6$ | $3/10$ | $3/13$ | $3/10$ |
| $D_\infty$ | $2/3$ | $1/5$ | $1/7$ | $2/9$ | $2/11$ | $1/13$ | $2/15$ |

So the binary expansion of $\tfrac13\Theta_3(1/2)$ is asymptotically $0101\cdots$, with defects of density zero. It is simply normal in base 2 but far from 2-normal.

**Proposition 5.4 (not disjunctive).** $\tfrac ad\Theta_3(1/b)$ and $\tfrac adE_b$ are not disjunctive in base $b$.

*Proof.* Fix $L$ and a shift $n$ whose next insertion is $p_k=n+r$, with coefficient $c_k$: $c_k=\pm1$ for $E_b$, $c_k=2$ for $\Theta_3$. Then
$x_n=\{b^n\tfrac adz\}=\bigl\{\tfrac{\alpha_n}d+\tfrac{a(c_k+R_k)}{d\,b^r}\bigr\}$. Here $\alpha_n=aI_n\bmod d$ is the atom, and $R_k$ is the tail after $p_k$, rescaled by $b^{p_k}$. The gaps between insertions tend to infinity, so $R_k\to0$.

For $\Theta_3$ we have $R_k>0$. For $E_b$, $\operatorname{sgn}(R_k)=c_{k+1}$, and all four pairs $(c_k,\operatorname{sgn}R_k)$ recur. The reason is that $P(K)$ is followed by $P(-K)$ with the same sign, $P(-K)$ is followed by $P(K+1)$ with the opposite sign, and both signs of $c_k$ recur.

Put $R=L+\lceil\log_b(4|a|d)\rceil$ and take $k$ so large that $|aR_k|<b^{-L}$.

- *Case $r\le R$.* The point $\beta=\tfrac{\alpha_n}d+\tfrac{ac_k}{d\,b^r}$ has denominator dividing $d\,b^r$. So its distance to an endpoint $j\,b^{-L}$ of a length-$L$ cylinder is either 0 or at least $1/(d\,b^{\max(r,L)})$. The perturbation $|aR_k|/(d\,b^r)$ is smaller than $b^{-L-r}/d$. Hence the word is determined by $\beta$, together with $\operatorname{sgn}(aR_k)$ when $\beta$ is an endpoint, that is, by $(\alpha_n,r,c_k,\operatorname{sgn}R_k)$. This gives at most $4dR$ words for $E_b$ and at most $dR$ for $\Theta_3$.

  Both signs of $R_k$ genuinely matter. When $\alpha_nb^r+ac_k\equiv0\pmod d$ and $r\le L$, the point $\beta$ is a cylinder endpoint.
- *Case $r>R$.* The perturbation is at most $3|a|/(d\,b^r)<1/(d\,b^L)$. A nonzero atom $\alpha/d$ lies at distance at least $1/(d\,b^L)$ from every endpoint (since $\gcd(d,b)=1$), so its word is that of $\alpha/d$, giving at most $d-1$ words. The atom 0 gives $0^L$ or $(b-1)^L$ according to $\operatorname{sgn}(ac_k)$. That is at most 2 words for $E_b$ and 1 for $\Theta_3$.

So at most $4dR+d+1$ (for $E_b$), resp. $dR+d$ (for $\Theta_3$), words of length $L$ occur infinitely often. This is $O_{a,b,d}(L)<b^L$ for large $L$. $\square$

*Check.* For $E_2$ ($d=1$, $a=1$, $b=2$) the recurrent words of length $L$ are exactly the binary words of $\{c\,2^{-r}(1+s\varepsilon)\}$ with $c,s\in\{\pm1\}$ and $1\le r\le L$, and there are exactly $4L-4$ of them. At $r=2$, for instance, the words are $010^{L-2}$, $001^{L-2}$, $101^{L-2}$ and $110^{L-2}$. For $L=8$ there are 28 words, within the bound $4R+2=42$ ($R=10$). The 28 words exceed the value $d(R+2)=12$ claimed in an earlier draft, so that bound was false. The script compares this predicted set with the words of 20,000 certified bits of $E_2$ past $P(-30)$, for $L=3,\dots,11$ (*finite computation* confirming the structural count).

## 6. Derivative scalings

**Theorem 6.1.** Let $d$ and $t=\operatorname{ord}_d(b)$ be odd, and $j\ge0$. Then the limit word laws of $\tfrac adD^jE_b$ and $\tfrac adD^jE_b^3$ in base $b$ are complement-symmetric. In base 2 these numbers are simply normal.

*Proof.* Put $T=\operatorname{lcm}(t,d)$, which is odd. Then $P(i+T)-P(i)=T(6i+3T-1)/2$ and $T_{i+T}-T_i=T(2i+T+1)/2$ are integer multiples of $T$. So $P(i)^j$, $T_i^j$, $2i+1$ and the powers of $q$ are $T$-periodic modulo $d$, while $(-1)^T=-1$. Hence the term sequences are antiperiodic with antiperiod $T$. For the cube, $\mathrm{tm}_3(T-1-i)=-\mathrm{tm}_3(i)$ as in F22. The proof of F22 Theorem 5.3 then goes through with $t$ replaced by $T$: $A(k+T)=-A(k)$ and $V(k+T)=-V(k)$, the factors $b^{P(\pm(k+T))}$ and $b^{T_{k+T}}$ are unchanged, and the run signs flip. $\square$

**Content.** Every coefficient $(2k+1)T_k^j$ of $D^jE^3$ with $j\ge1$ is divisible by 3, since one of $k,k+1,2k+1$ is. The $k=1$ coefficient is $-3\cdot1^j=-3$, so the content is exactly 3 for every $j\ge1$. So $\tfrac adD^jE_b^3=\tfrac a{d'}F$ with $d'=d/\gcd(d,3)$ and $F=\tfrac13D^jE_b^3$ an alternating integer series on the triangular numbers. For instance $\tfrac a3DE_2^3=aE_2^2DE_2$, which is simply normal in base 2 by F22 Theorem 2, and $\tfrac a{21}DE_2^3=\tfrac a7E_2^2DE_2$, where $\operatorname{ord}_7(2)=3$.

**Corollary 6.2 (reduced denominator).** Let $j\ge1$ and let $d$ be odd and coprime to $b$ with $3\parallel d$. Put $d'=d/3$ and suppose $\operatorname{ord}_{d'}(b)$ is odd (with $\operatorname{ord}_1(b)=1$). Then the limit word law of $\tfrac adD^jE_b^3$ in base $b$ is complement-symmetric. In base 2 the number is simply normal. Examples are $d=21,69,93$ for $b=2$.

*Proof.* Write $\tfrac adD^jE_b^3=\tfrac a{d'}F$ with $\gcd(a,d')=1$. F22 Lemma 2.1 applies to $F$ as to $D^jE_b^3$, since the coefficients are polynomial in $k$ and the gaps grow linearly. So Theorem 0.1 gives the signed automaton for $\tfrac a{d'}F$.

If $d'=1$, every head is $\equiv0$. The classes have equal weight and alternating run signs $(-1)^{k+1}$, so $w_0^+=w_0^-$.

If $d'\ge2$, then $3\nmid d'$, so 3 is invertible mod $d'$, and the term sequence of $F$ mod $d'$ is $3^{-1}\mathrm{tm}_3$. Multiplying by the unit $3^{-1}$ preserves the antiperiodicity with odd antiperiod $T=\operatorname{lcm}(\operatorname{ord}_{d'}(b),d')$ and the reflection $\mathrm{tm}_3(T-1-i)=-\mathrm{tm}_3(i)$. These are the only inputs to the proof of Theorem 6.1, which therefore applies with $d'$ in place of $d$. $\square$

When $9\mid d$, the reduced series still has the factor 3 in $d'$ and the argument does not apply.

*Finite data (exact laws, odd $d\le45$, base 2).* For $j=1,2$, $\tfrac adD^jE_2$ is simply normal exactly for $d\in\{7,23,31\}$, and $\tfrac adD^jE_2^3$ exactly for $d\in\{3,7,21,23,31\}$, i.e. exactly when the reduced denominator has odd order. The "if" part for $d=3,21$ is Corollary 6.2, which the script also confirms for $d=69,93$. Negation symmetry holds in every case. Examples: $f_0(\tfrac13DE_2)=\tfrac7{12}$, $f_0(\tfrac13D^2E_2)=\tfrac{19}{36}$, $f_0(\tfrac15DE_2^3)=\tfrac{19}{40}$. The analogue of Conjecture 5.5 ("only if", with the reduced denominator) is **Open**. Disjunctivity of $\tfrac adD^jE_b$ ($j\ge1$) and $\tfrac adE_b^3$ is expected from planted windows as in F22 Theorem 2.4, but the window reads the sum of a periodic block and $\lfloor ac/d\rfloor$, and we have not completed the argument: **Open**.

## 7. $\tfrac a2E_b^2$ in odd radix

**Theorem 7.1.** Let $b\ge3$ be odd and $a$ odd. In base $b$, for every $L$,

```math
f_{((b-1)/2)^L}\bigl(\tfrac a2E_b^2\bigr)\to\frac23,\qquad f_{0^L}+f_{(b-1)^L}\to\frac13,
```

and every other word has frequency $\to0$. In particular $\tfrac a2E_b^2$ is not simply normal in base $b$, and $D_\infty=\tfrac23$.

*Proof.* Since $E(q)^2\equiv E(q^2)\pmod2$, $a_2(m)$ is odd iff $m=2P(j)$. As $b$ is odd, $I_n\equiv\#\{j:2P(j)\le n\}\pmod 2$. This count is odd exactly for $n/2\in[P(-k),P(k+1))$, a union of intervals of length $2k+1$ alternating with intervals of length $k$, so the atom $\tfrac12$ has density $\frac23$. For $E_b^2$, $B_L(N)=o(N)$ (F22 Theorem 4.3), so $x_n=\{\tfrac a2I_n+\tfrac a2\tau_n\}$ lies within $o(1)$ of $\frac12$ (an interior point in odd base, with expansion $((b-1)/2)^\infty$) or of $0$, outside $o(N)$ shifts. Atom changes occur at the $O(\sqrt N)$ points $2P(j)$. For $D_\infty$: the point mass $\frac23$ gives $D^+=\frac23$, and every other interval gives at most $\frac12$. $\square$

How $\frac13$ splits between $0^L$ and $(b-1)^L$ is the oriented gap-weighted sign proportion of $E_b^2$ restricted to atom-0 shifts. It is **Open**, like the simple normality of $E_2^2$ (F22 §4).

*Finite data.* $E(q)^2\equiv E(q^2)\pmod2$ was checked for $n\le4400$. Below $4096$, 2,738 shifts carry the atom $\tfrac12$ ($2N/3=2730.7$). The certified base-3 digits of $\tfrac12E_3^2$ at $N=4000$ give $f_0=0.3205$, $f_1=0.4360$, $f_2=0.2435$. At atom-$\tfrac12$ shifts (2,668 of them) the digit is 1 with share $0.5412$; at atom-0 shifts (1,332) the digit is 0 or 2 with share $0.7748$. *Finite measurement:* at this scale the support of $a_2$ is dense and the tails are not small, so these numbers are far from the limit and are not evidence about it.

## 8. A4: everywhere-nonnegative reflections

Let $a_{r,M}=\tau_{r,M}-\tau_{M-r,M}=1*w_{r,M}$, so that $F_b(a_{r,M})$ is the normalized $q$-digamma reflection (F22 §3, kernel-verified identification).

**Theorem 8.1.** For $1\le r<M/2$, $a_{r,M}(n)\ge0$ for all $n$ iff $r\mid M$ and $M/r\in\{3,4,6,8,12,24\}$. In every other case $a_{r,M}(n)<0$ for infinitely many $n$, so "eventually nonnegative" coincides with "everywhere nonnegative". In the nonnegative cases $f_{0^L}\to1$ in every base $b$ (F22 Corollary 1.2). Otherwise $F_b(a_{r,M})$ is in the signed regime of F22 Theorem 3.5.

*Proof.* Put $g=\gcd(r,M)$, $M'=M/g$ and $r'=r/g$. Then $a_{r,M}(n)=a_{r',M'}(n/g)$ (F22 Proposition 3.1), with $r'<M'/2$. If $r'\ne1$, then $r'\not\equiv\pm1\pmod{M'}$, and a prime $p\equiv-r'$ gives $a(p)=-1$ (F22 Proposition 3.3). If $r'=1$, F22 Theorem 3.2 gives nonnegativity iff $\lambda(M')=2$, i.e. $M'\mid24$. For recurrence: if $q\equiv1\pmod M$ is prime and $q\nmid n$, then $w(qd)=w(d)$, so $a(nq)=2a(n)$. $\square$

*Finite data.* For $3\le M\le60$ there are 59 nonnegative pairs and 811 signed pairs. For each signed pair the script constructs an explicit $n$ with $a_{r,M}(n)<0$, by the prime constructions of F22 Theorem 3.2 (Cases A, B) or Proposition 3.3, and evaluates $a$ exactly by a residue convolution, cross-checked against direct divisor sums for $n<10^7$. Nonnegativity of the six reduced pairs was checked for $n\le20000$.

## 9. A4: arithmetic sign-flip involutions

Let $G=(\mathbb Z/M')^\times$, $\varphi=|G|$, and recall $a_{r,M'}=\frac2\varphi\sum_{\chi\ \mathrm{odd}}\bar\chi(r)(1*\chi)$ (F22 Proposition 3.1). For $\gcd(n,m)=1$,

```math
a_{r,M'}(nm)=\frac2\varphi\sum_{\chi\ \mathrm{odd}}\bar\chi(r)\,(1*\chi)(m)\,(1*\chi)(n).\tag{9.1}
```

**Lemma 9.1 (independence).** For any finite set of primes $Q$, the functions $n\mapsto(1*\chi)(n)$, $\chi$ odd, are linearly independent on the integers prime to $Q$.

*Proof.* Evaluate a relation $\sum c_\chi(1*\chi)=0$ at primes $p\notin Q$ in every class: $\sum c_\chi+\sum c_\chi\chi(g)=0$ for all $g\in G$. Summing over $g$ gives $\sum c_\chi=0$, since every odd $\chi$ is nontrivial. Then $\sum c_\chi\chi(g)=0$ for all $g$, so $c_\chi=0$ by orthogonality. $\square$

**Theorem 9.2 (universal flip).** The following are equivalent:

1. $-1$ is a square in $G$;
2. every real character modulo $M'$ is even;
3. for some unit $r$ there is $m\ge1$ with $a_{r,M'}(nm)=-a_{r,M'}(n)$ for all $n$ prime to $mM'$.

If $u^2\equiv-1$ and $q_1\ne q_2$ are primes $\equiv u$, then $m=q_1^2q_2^2$ satisfies (3) for every $r$, and $a_{r,M'}(nq_1^2)=a_{u^{-1}r,M'}(n)$ (transport).

*Proof.* (1)⇒(3): for odd $\chi$, $\chi(u)^2=\chi(-1)=-1$, so $(1*\chi)(q^2)=1+\chi(u)+\chi(u)^2=\chi(u)$ and $(1*\chi)(q_1^2q_2^2)=-1$. Apply (9.1). (3)⇒(2): by (9.1) and Lemma 9.1, $(1*\chi)(m)=-1$ for every odd $\chi$. That is impossible for a real odd $\chi$, since $(1*\chi)\ge0$ (F22 Proposition 1.1). (2)⇒(1): $G/G^2$ is an elementary abelian 2-group, so if $-1\notin G^2$ some character of $G/G^2$ takes the value $-1$ at $-1$, and it is real and odd. $\square$

The moduli $M'\le60$ with $\lambda(M')>2$ and $-1$ a square are $5,10,13,17,25,26,29,34,37,41,50,53,58$. Both identities were checked on 52,870 triples $(M',r,n)$ with $n<400$. For $M'=5$: $u=2$, $q_1,q_2=2,7$, $m=196$.

**Theorem 9.3 (unit values).** If $\chi(q)=\zeta\ne1$ has order $o$ and $e=o-2$, then $(1*\chi)(q^e)=\sum_{i=0}^{o-2}\zeta^i=-\zeta^{-1}$.

**Theorem 9.4 (single complex characters).** For every character $\chi$ of order $\ge3$ there is $m$ with $(1*\chi)(m)=-1$. Hence $\operatorname{Re}(c\,(1*\chi))(nm)=-\operatorname{Re}(c\,(1*\chi))(n)$ for all $c\in\mathbb C$ and all $n$ prime to $m$. For a real $\chi$ no such $m$ exists.

*Proof.* Choose $\zeta_1\zeta_2\zeta_3=1$ with all $\zeta_i\ne1$ in the image of $\chi$, which is possible once the order is $\ge3$, and three distinct primes $q_1,q_2,q_3$ with $\chi(q_i)=\zeta_i$. Distinctness is needed because often $\zeta_1=\zeta_2$, and it makes $(1*\chi)(\prod q_i^{e_i})=\prod(1*\chi)(q_i^{e_i})$. By Theorem 9.3, $\prod(-\zeta_i^{-1})=-1$. $\square$

**Theorem 9.5 (dominant flip, cyclic $G$).** Let $G$ be cyclic with $\varphi\ge4$, and let $\chi_0$ be a faithful character (it is odd). Let $\mathcal D$ be the set of $n$ prime to $M'$ with $(1*\chi)(n)=0$ for every odd non-faithful $\chi$. On $\mathcal D$, $a_{r,M'}(n)=\frac2\varphi\operatorname{Tr}_{\mathbb Q(\zeta_\varphi)/\mathbb Q}\bigl(\bar\chi_0(r)(1*\chi_0)(n)\bigr)$. If $m$ is as in Theorem 9.4 for $\chi_0$, then $(1*\chi_0^j)(m)=-1$ for every faithful $\chi_0^j$, by Galois conjugation, and $a_{r,M'}(nm)=-a_{r,M'}(n)$ for $n\in\mathcal D$ prime to $m$.

This covers the cyclic moduli without $\sqrt{-1}$, where Theorem 9.2 fails. The script builds $m$ (three prime powers), verifies $(1*\chi_0)(m)=-1$ in $\mathbb Z[x]/\Phi_\varphi$, and checks the flip on 32,344 triples:

| $M'$ | $\varphi$ | $m$ | dominant share of support ($n<1500$, $(n,mM')=1$) |
| --- | --- | --- | --- |
| 7 | 6 | $2\cdot23\cdot37$ | 316/475 |
| 9 | 6 | $13\cdot31\cdot67$ | 488/698 |
| 11 | 10 | $2^8\cdot13^8\cdot3^3$ | 212/380 |
| 14 | 6 | $23\cdot37\cdot79$ | 312/468 |
| 18 | 6 | $7\cdot43\cdot61$ | 190/331 |
| 19 | 18 | $7\cdot83\cdot197$ | 159/1123 |
| 22 | 10 | $7^8\cdot29^8\cdot31^3$ | 247/495 |
| 23 | 22 | $5^{20}\cdot97^{20}\cdot127^9$ | 649/1104 |
| 27 | 18 | $37\cdot199\cdot307$ | 151/920 |
| 31 | 30 | $149\cdot211\cdot397$ | 2/1387 |

The dominant share is small for $M'=19,27,31$ at this scale because non-faithful characters of kernel size $e$ have support of order $X/(\log X)^{e/\varphi}$. These sets are negligible only asymptotically (*finite measurement*).

## 10. A4: densities of signs and digit consequences

**Theorem 10.1 (cyclic moduli).** Let $(\mathbb Z/M')^\times$ be cyclic with $\varphi(M')\ge4$ (so $M'=p^k$ or $2p^k$ with $p$ an odd prime, $M'\ne3,6$), and let $r$ be a unit. Then $S(X)=\#\{n\le X:a_{r,M'}(n)\ne0\}\asymp X/(\log X)^{1/\varphi}$, and

```math
\liminf_{X\to\infty}\frac{\#\{n\le X:a_{r,M'}(n)>0\}}{S(X)}>0,\qquad \liminf_{X\to\infty}\frac{\#\{n\le X:a_{r,M'}(n)<0\}}{S(X)}>0 .
```

The same holds for $a_{r,M}$ with $M=gM'$, $r=gr'$.

*Proof.* (i) The support lies in $U=\{n:v_p(n)\text{ even for all }p\equiv-1\pmod{M'}\}$ (F22 §3), a multiplicative set of prime density $1-1/\varphi$, so $S(X)\ll X/(\log X)^{1/\varphi}$ by Wirsing's theorem. (ii) The non-dominant part lies in $\bigcup\operatorname{supp}(1*\chi_0^j)$ over odd $j$ with $e=\gcd(j,\varphi)\ge3$, whose count is $\ll X/(\log X)^{3/\varphi}$. (iii) Transport: for each $g\in G$, Theorem 9.3 gives a product $\Pi_g$ of two prime powers with $(1*\chi_0)(\Pi_g)=\chi_0(g)$, taking $\zeta_1\zeta_2=\chi_0(g)^{-1}$ with $\zeta_i\ne1$. When $\varphi=4$, a factor with $\zeta_i=-1$ has exponent $e_i=o-2=0$, so $\Pi_g$ may be a single prime power; for $g=1$ take $\Pi_1=1$. Choose the auxiliary primes disjoint for different $g$, and let $Q$ be their product. The $\Pi_g$ are then pairwise distinct $Q$-smooth integers. Indeed $\Pi_g=1$ iff $g=1$, because $\chi_0$ is faithful, and different $g\ne1$ use disjoint primes with at least one positive exponent. On $\mathcal D$, $a_r(n\Pi_g)=a_{rg^{-1}}(n)$. (iv) Let $V_0'$ be the multiplicative set $\operatorname{supp}(1*\chi_0)$ restricted to $n$ prime to $QM'$, as $\mathcal D$ requires $\gcd(n,M')=1$. Its prime density is still $1-1/\varphi$, so Wirsing's theorem gives $|V_0'(X)|\asymp X/(\log X)^{1/\varphi}$. For $n\in V_0'\cap\mathcal D$ put $z=(1*\chi_0)(n)\ne0$. The values $\{\bar\chi_0(s):s\in G\}=\mu_\varphi$ span $\mathbb Q(\zeta_\varphi)$ over $\mathbb Q$, and the trace form is nondegenerate, so $\operatorname{Tr}(\bar\chi_0(s)z)\ne0$ for some $s$. By oddness ($a_{-s}=-a_s$) both signs occur. Mapping $n\mapsto n\Pi_{rs^{-1}}$ with $a_s(n)>0$ is injective, so $\#\{n\le Y:a_r(n)>0\}\ge|(V_0'\cap\mathcal D)(Y/\Pi_{\max})|\gg Y/(\log Y)^{1/\varphi}$. Negative values are handled the same way. $\square$

The input is Wirsing's mean-value theorem for nonnegative multiplicative functions (E. Wirsing, *Math. Ann.* 143 (1961)). No Selberg–Delange asymptotics are needed. For $M'=5$ the universal flip $n\mapsto196n$ of Theorem 9.2 gives the same conclusion directly.

**Theorem 10.2 (real type).** If $\lambda(M')=2$ and $r'\not\equiv\pm1$ (the pairs $(8,3),(12,5),(24,5),(24,7),(24,11)$ and their multiples), then both signs have positive relative density. The positive proportion tends to $\sum_{\chi\ \mathrm{odd},\,\chi(r')=1}K_\chi/\sum_{\chi\ \mathrm{odd}}K_\chi$, with $\chi$ running over the odd characters mod $M'$ and $K_\chi$ the Wirsing constant of $\operatorname{supp}(1*\chi)$.

*Proof.* Off pairwise intersections of the supports of the odd characters, which have count $\ll X/(\log X)^{3/4}$, $a_{r'}=\frac2\varphi\chi(r')(1*\chi)$ has sign $\chi(r')$. Both values occur among the odd $\chi$, because $\sum_{\chi\ \mathrm{odd}}\chi(r')=0$ for $r'\not\equiv\pm1$. The case $\gcd(r,M)>1$ follows from $a_{r,M}(n)=a_{r',M'}(n/g)$. This generalizes F22 Proposition 3.6. $\square$

**Theorem 10.3 (both constant words; Conditional).** Assume

> **(S$_U$)** $\sum_{h\le H}\#\{n\le N:n,\,n+h\in U\}\le C\,HN/(\log N)^{2\kappa}$ for $1\le H\le N$,

with $U=U_{M'}$ and $\kappa=1/\varphi(M')$ in the setting of Theorem 10.1, or $U=\bigcup_{\chi\ \mathrm{odd}}\operatorname{supp}(1*\chi)$ and $\kappa=\frac12$ in the setting of Theorem 10.2. Then for $z=F_b(a_{r,M})$, in every base $b\ge2$ and for every $L$, $\liminf f_{0^L}(N)>0$ and $\liminf f_{(b-1)^L}(N)>0$. In base 2 both binary digits have positive lower frequency.

*Proof.* This is F22 Theorem 4.4 with $\frac34$ replaced by $\kappa$. Positive (resp. negative) points in a window $(N/K,N]$ number $\gg N/(\log N)^\kappa$ (Theorems 10.1–10.2, using fixed-ratio windows). (S$_U$) with $H=\eta(\log N)^\kappa$ isolates most of them. Markov's inequality with $\sum_{n\le N}|a(n)|\ll N\log N$ removes those with $|a(n)|>(\log N)^2$. Isolated points have $|\tau|<1$ outside $O(N(\log N)b^{-H})$ exceptions. Each remaining point forces the constant word on $\gg(\log N)^\kappa$ preceding shifts (F22 Lemmas 0.1, 0.3). $\square$

(S$_U$) is the analogue of Theorem S of [`partitions-carry-and-lemma-s.md`](../phase22/partitions-carry-and-lemma-s.md). That proof is written for $12n+1$ with exponent $\frac34$. Its Selberg-sieve argument is expected to transfer to $U_{M'}$, but the transfer is not written out here, hence **Conditional**.

**What the flips do not give.** Base-2 simple normality of $F_2(a_{r,M})$ is equivalent to the oriented gap-weighted proportion $\rho_+\to\frac12$ (F22 Theorem 3.5). The map $n\mapsto nm$ changes scale and does not preserve gaps, so it says nothing about $\rho_+$. For the real type, (H$_{\rm gap}$) of F22 predicts non-simple-normality. **Open.**

*Finite data* ($X=2^{15}$, exact counts):

| $(M,r)$ | support$/X$ | positive$/$support | negative$/$support |
| --- | --- | --- | --- |
| (5,1) | 0.5031 | 0.8970 | 0.1030 |
| (5,2) | 0.4649 | 0.5966 | 0.4034 |
| (13,1) | 0.7395 | 0.9448 | 0.0552 |
| (7,3) | 0.5053 | 0.5947 | 0.4053 |
| (7,1) | 0.5874 | 0.9239 | 0.0761 |
| (8,3) | 0.3880 | 0.5578 | 0.4422 |
| (12,5) | 0.4310 | 0.5293 | 0.4707 |

*Finite measurement.* For $r=1$ the negative share is small at this scale, although Theorem 10.1 proves it has a positive liminf. The flip $n\mapsto nm$ moves mass between scales $X$ and $mX$, and the support densities ($0.4$–$0.7$) are far from their limit 0.

## 11. The conjugation idea for $\operatorname{Im}(1*\chi)$

Let $\chi$ be the quartic character mod 5 with $\chi(2)=i$. Then $\operatorname{Re}(1*\chi)=a_{1,5}$ and $\operatorname{Im}(1*\chi)=a_{2,5}=\tau_{2,5}-\tau_{3,5}$ (checked for $n\le32768$). So the proposed sequence is the $q$-digamma reflection $(M,r)=(5,2)$. Its support is $\asymp X/(\log X)^{1/4}$ (Theorem 10.1).

- **Conjugation.** $\sigma:\chi\mapsto\bar\chi$ gives $\operatorname{Im}(1*\bar\chi)=-\operatorname{Im}(1*\chi)$ identically. This is a relation between **two** numbers, $F_b(\operatorname{Im}(1*\bar\chi))=-F_b(\operatorname{Im}(1*\chi))$, whose digit laws are complements of each other. It carries no information about the digits of either number alone, so it cannot prove $\liminf f_0>0$, simple normality or a bias.
- **Arithmetic flip.** The useful symmetry acts on the index $n$: $(1*\chi)(196)=(1*\chi)(2^2)(1*\chi)(7^2)=i\cdot i=-1$. So $a_{2,5}(196n)=-a_{2,5}(n)$ for $n$ prime to 14, and $a_{1,5}(4n)=-a_{2,5}(n)$ for odd $n$. These give positive relative density for both signs (Theorem 10.1, Paper proof) and positive lower frequency for both $0^L$ and $(b-1)^L$ in every base $b$, conditionally on (S$_U$) for $U_5$ with $\kappa=\frac14$ (Theorem 10.3).
- **Not obtained.** Base-2 simple normality of $A_{2,5}(2)-A_{3,5}(2)$ and any exact bias remain **Open**. The unweighted sign proportion is expected to tend to $\frac12$ (Delange-type equidistribution of $\arg(1*\chi)$). At $X=2^{15}$ it measures $0.5966$ (finite measurement).

## 12. Lean blueprint: finite cores for `NormalityChecker/Phase23Cores.lean`

Statements only; none is written or checked. They build on `Phase22Cores` (`pentTerm`, `pentHeadSum`, `cubeTerm`, `triNum`, `eulerAutomaton_snd_add_order`, `cubeHeadSum_add_period`).

```lean
namespace NormalityChecker.Phase23Cores

/-- ℤ-indexed prefix sums of `pentTerm`; `pentMinus b d k = Σ_{j=1-k}^{k} pentTerm b d j`. -/
def pentPrefix (b d : ℕ) : ℤ → ZMod d := sorry
def pentMinus (b d : ℕ) (k : ℤ) : ZMod d := pentPrefix b d (k + 1) - pentPrefix b d (1 - k)
def pentPlus (b d : ℕ) (k : ℤ) : ZMod d := pentPrefix b d (k + 1) - pentPrefix b d (-k)

/-- Theorem 1.1, formal core (Euler type). -/
theorem pentMinus_neg (b d : ℕ) (k : ℤ) : pentMinus b d (-k) = - pentMinus b d k
theorem pentPlus_neg (b d : ℕ) (k : ℤ) : pentPlus b d (-k) = - pentPlus b d (k - 1)

/-- Theorem 1.1, cube and theta reflections. -/
theorem cubeTermZ_reflect (b d : ℕ) (i : ℤ) : cubeTermZ b d (-1 - i) = cubeTermZ b d i
theorem thetaHead_reflect (b d : ℕ) (k : ℤ) : thetaHeadZ b d (-1 - k) = - thetaHeadZ b d k

/-- Lemma 2.1(1): vanishing period sum for odd `d`. -/
theorem sum_pentTerm_two_order_eq_zero {b d : ℕ} [NeZero d] (hcop : Nat.Coprime b d)
    (hd : Odd d) : ∑ j ∈ Finset.range (2 * orderOf (b : ZMod d)), pentTerm b d j = 0

/-- Lemma 2.1(1), even order: the `t`-shift multiplies by `ι = b^(t/2)`. -/
theorem pentTerm_add_order_of_even {b d : ℕ} [NeZero d] (hcop : Nat.Coprime b d)
    (he : Even (orderOf (b : ZMod d))) (j : ℤ) :
    pentTerm b d (j + orderOf (b : ZMod d)) =
      (b : ZMod d) ^ (orderOf (b : ZMod d) / 2) * pentTerm b d j

/-- Theorem 2.2, combinatorial core: the parity of a symmetric signed zero count. -/
theorem signed_count_odd_iff {h : ℕ} (hh : 0 < h) (z : ZMod (2 * h) → ℤ)
    (h01 : ∀ k, z k = 0 ∨ z k = 1) (hsym : ∀ k, z (-k) = z k) (h0 : z 0 = 1) :
    Odd (∑ k : ZMod (2 * h), (-1 : ℤ) ^ k.val * z k) ↔ z h = 0

/-- Theorem 5.2: theta heads never vanish mod 3. -/
theorem thetaHead_mod_three_ne_zero (k : ℕ) :
    (1 + 2 * ∑ j ∈ Finset.Icc 1 k, (-1 : ZMod 3) ^ j) ≠ 0

/-- Theorem 5.3: uniform digit count on the units when `p ≡ 1 [MOD b]`. -/
theorem card_digit_units {b p e : ℕ} (hb : 2 ≤ b) (hp : p % b = 1) (he : e < b) :
    ((Finset.Icc 1 (p - 1)).filter (fun c => b * c / p = e)).card = (p - 1) / b

/-- §6: the content of `D^j E^3`. -/
theorem three_dvd_cube_deriv_coeff (k : ℕ) : 3 ∣ (2 * k + 1) * triNum k

/-- Theorem 9.3: unit values of geometric sums at roots of unity. -/
theorem geom_sum_root_of_unity {K : Type*} [Field K] {ζ : K} {o : ℕ} (ho : 2 ≤ o)
    (hζ : ζ ^ o = 1) (h1 : ζ ≠ 1) : ∑ i ∈ Finset.range (o - 1), ζ ^ i = - ζ⁻¹

/-- Theorem 9.2, (1) ⇒ (3): the universal flip for antisymmetric Lambert coefficients. -/
theorem antisymLambert_flip {M r q₁ q₂ n : ℕ} (u : ZMod M) (hu : u ^ 2 = -1)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) (h₁ : (q₁ : ZMod M) = u)
    (h₂ : (q₂ : ZMod M) = u) (hn : Nat.Coprime n (q₁ * q₂)) :
    antisymLambert M r (n * q₁ ^ 2 * q₂ ^ 2) = - antisymLambert M r n

/-- Theorem 7.1: parity of the generalized pentagonal count. -/
theorem genPent_count_odd_iff (X : ℕ) :
    Odd ((Finset.Icc (-(X : ℤ)) X).filter (fun j => genPent j ≤ X)).card ↔
      ∃ k : ℕ, genPent (-(k : ℤ)) ≤ X ∧ X < genPent ((k : ℤ) + 1)
```

`cubeTermZ` and `thetaHeadZ` are the $\mathbb Z$-indexed versions of `cubeTerm` and $B(k)$, and `antisymLambert M r n` is $\sum_{d\mid n}(\mathbf 1_{d\equiv r}-\mathbf 1_{d\equiv-r})$. The reflections, `signed_count_odd_iff`, `thetaHead_mod_three_ne_zero`, `card_digit_units` and `three_dvd_cube_deriv_coeff` are elementary. `sum_pentTerm_two_order_eq_zero` needs the CRT induction of Lemma 2.1. Decidable certificates, for example that $A^-_{113}(56)\equiv0\pmod{113}$ in base 10, can be added by `decide`.

## 13. Verification record

```sh
python -B scripts/phase23_rational_signed.py
```

Standard library only, exact `int`/`Fraction` arithmetic. The run takes about 5 s, performs 214,603 checks and exits 0. It verifies:

- **R1.** All 32,600 base-2 laws (odd $d\le200$): $\sigma\equiv0$, negation symmetry, the parity formulas and closed forms for $f_0$, the half-period test, "simply normal $\iff$ odd order", and exact $D_\infty$.
- **R2.** The prime reduction on 93 pairs; no 2-exceptional prime $\le20000$ (E) or $\le3000$ (E$^3$); the base-10 exceptional prime 113 ($t=112\equiv0\pmod4$, zeros of $A^-$ at $k=29,56,83,112$) with its complement-symmetric law; the base-3 cube-exceptional prime 5.
- **R3.** The parity formula in bases 3, 5, 10; 42,296 laws in bases 3–10, none simply normal.
- **R4.** Theta laws: symmetry, the odd-order obstruction, the mod-3 theorem, the base-2 list of 48 denominators, lists for $b\in\{3,4,5,6,7,10\}$ (each listed $d$ simply normal for every numerator and sign), the prime criterion on 30 pairs, exact laws and $D_\infty$, and the Proposition 5.4 word count for $E_2$ ($4L-4$ recurrent words, $L=3,\dots,11$).
- **R5.** Derivative laws for $j=1,2$, odd $d\le45$; the content 3 of $D^jE^3$ for $j\le6$; Corollary 6.2 for $d=3,21,69,93$; and for 8 even $d$ with $b$ odd and $v_2(d)>v_2(t)$, the term period $2\operatorname{lcm}(t,d)$ of $D^jE_b$, the failure of $\operatorname{lcm}(2t,d)$, period-independence of the law, and the Theorem 1.1 symmetry. For example, $\tfrac12DE_3$ has base-3 digit law $(\tfrac13,\tfrac12,\tfrac16)$, whereas the wrong period would give $(\tfrac16,\tfrac56,0)$.
- **R6.** $E^2\equiv E(q^2)\pmod2$, the atom-$\tfrac12$ count, and certified base-3 digits of $\tfrac12E_3^2$.
- **S1–S4.** The classification for $M\le60$ with witnesses; the universal flip and transport; dominant flips for 10 cyclic moduli with $(1*\chi_0)(m)=-1$ verified in $\mathbb Z[x]/\Phi_\varphi$; $\operatorname{Re}/\operatorname{Im}(1*\chi)=a_{1,5}/a_{2,5}$; sign statistics.

Finite digit and sign statistics are measurements at accessible scales and are not evidence for limits. Exact automaton laws are proofs of the stated limit values by Theorem 0.1. No cross-model review is claimed here; a cross-model review would not be independent human peer review.

## 14. Open problems

1. Conjecture 5.5 (base 2, $E_2$ and $E_2^3$) for all odd $d$. Equivalently, decide whether a balanced 2-exceptional prime exists. Heuristically one does (§3.5); none exists below $20000$ (resp. $3000$).
2. A rational scaling of $E_b$ or $E_b^3$ that is simply normal in a base $b\ge3$ (none among 42,296 laws). For $\Theta_3$ such scalings exist (Theorem 5.3).
3. Infinitely many primes satisfying Theorem 5.3 for a fixed $b$, e.g. $b=3$; equivalently, zero-freeness of the theta head sums modulo infinitely many primes $p\equiv7\pmod{12}$ with 3 a primitive root.
4. The "only if" direction of Theorem 6.1, and disjunctivity of $\tfrac adD^jE_b$ ($j\ge1$) and $\tfrac adE_b^3$.
5. The split of $\tfrac13$ between $0^L$ and $(b-1)^L$ for $\tfrac a2E_b^2$ (Theorem 7.1).
6. Prove (S$_U$) for $U_{M'}$, which would make Theorem 10.3 unconditional; and decide positive relative density of both signs for non-cyclic $M'$ with $\lambda(M')>2$ (e.g. $M'=15,16,20,21$).
7. Base-2 simple normality, or an exact bias, for the signed reflections, including $\operatorname{Im}(1*\chi)$ mod 5 (§11).
