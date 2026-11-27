# Referee report on Phase 23 Track C1–C4

**Reviewer:** `claude-opus-5-5` (cross-provider referee; author of the audited track: `gpt-6.2-astra`).
**Audited files (read-only, untracked in the working tree on top of `0342f1fdc573e38804e4f321a68776a6d91350da`):**
[`notes/phase23/nonlinear-multivariate-and-denser-mu.md`](../nonlinear-multivariate-and-denser-mu.md) (blob `ded7f70a`) and
[`scripts/phase23_nonlinear_short_orbits.py`](../../../scripts/phase23_nonlinear_short_orbits.py) (blob `3daeac3f`).
Line numbers below refer to these blobs.

| Sub-track | Verdict |
|---|---|
| **C1** (Theorem 1 irrationality, Theorem 2 jump law, aggregate law (A)) | **ACCEPT AFTER REVISION** |
| **C2** (packet lemma, eligible starts, cubic structure, conditional criteria) | **ACCEPT AFTER REVISION** |
| **C3** (Theorem 3 multivariate effective rate, hybrid budget (3)) | **ACCEPT AFTER REVISION** |
| **C4** (Proposition 4, Lemma 5, Theorems 6 and 7: all degrees, all primes, $\mu=2$) | **ACCEPT AFTER REVISION** |

I found **no Critical issue**. After a line-by-line attack, every theorem in the note survives as a mathematical statement. That includes the extraordinary C4 claims: $\mu=2$, positions $n_j\asymp j\sqrt{\log j}$ with $n_{j+1}/n_j\to1$, persistent all-prime support, and power-saving normality of $P(V)$ for **every** nonconstant $P\in\mathbb Q[X]$. There is **one Major issue**. The only external input to Theorem 1 points to the wrong theorem number of the cited paper, and the theorem actually named is too weak to prove the result. The constant $390/449$ and the author list are correct. The remaining findings are Minor: exposition, notation, an unrecorded Phase 21 erratum, and gaps in the coverage of the finite checks.

"Critical" means a claim is false or unproved as stated. "Major" means a defect that must be fixed before the result can be relied on or cited: a wrong evidence pointer, a missing proof obligation or a mislabelled scope. "Minor" means a local correction where the argument is already available.

**Standing disclaimers.** Cross-model review is **not** independent human peer review. Finite computations, whether the script's or mine, are finite measurements or finite certificates. They **do not prove** any asymptotic statement. Earlier results used as inputs were checked only for their *statements*, against the Phase 21/22 notes; their proofs were audited in the earlier reviews and were not re-audited here. The inputs are Phase 21 Theorem Q, Proposition D, Theorem M and Lemma I, and Phase 22 Lemma A, Corollary B, Lemma D and Theorem S. I did not modify either audited file and did not commit anything.

---

## 0. Reproduction of the script

`python -B scripts/phase23_nonlinear_short_orbits.py` ran natively under Windows (Python 3.13.13). It **exited 0 in about 1.5 s** and printed `All exact checks passed.` The script is pure exact rational arithmetic, so its results do not depend on the platform. I did not repeat the run on the Hail Linux host.

Every number displayed in §9 of the note (lines 258–262) matches the printed output exactly:

| Note (line) | Claimed | Script output |
|---|---|---|
| 258 | square arrivals $p=3$: 643; $p=5$: 479; cube: 164 | 643 / 479 / 164 ✓ |
| 258 | surviving-pole packets 1871, 1200, 427 | 1871 / 1200 / 427 ✓ |
| 259 | residue counts $(1{:}9,2{:}29)$ for $p=3$; $(1{:}1,2{:}30,4{:}1)$ for $p=5$ | identical ✓ |
| 260 | square: 1044 ones, 1023 changes; cube: 983 ones, 1100 changes; denominator 2047 | identical ✓ |
| 261 | 32 words at $q=81$; residues $2,41,15,15,60\bmod 81$ | identical ✓ |
| 262 | 1422 corrections; 251 antichains; prefix denominators through shift 1023 in 3 radices | identical ✓ (`range(1, 2**10)`) |

I also read the script line by line. Its findings are in §6.

## 1. External inputs: verified against the sources

- **Dietmann–Elsholtz–Kalmynin–Konyagin–Maynard, "Longer gaps between values of binary quadratic forms" (IMRN, doi:10.1093/imrn/rnac130).** I read the five-author accepted manuscript in the Oxford Research Archive (PDF dated April 2022).
  - **Theorem 1** states $\limsup_n (s_{n+1}-s_n)/\log s_n\ge 390/449=0.868\ldots$ for the positive integers $s_n$ that are sums of two squares, so zero coordinates are allowed. Equivalently it states $g(X)\ge(390/449+o(1))\log X$. The logarithm is natural, since the constants arise from $\Phi(Y)=\exp((449/195+\epsilon)Y)$.
  - **Theorem 2** is the general fundamental-discriminant result. At $D=-4$, its explicit part A gives only $3/(8(1+\log2))\approx0.2215$.
  - For comparison, the two-author arXiv v2 (1810.03203) has the weaker constant $195/449$. The paper explains that a probabilistic refinement doubles it to $390/449$.
  - So the constant, the authors and the logarithm convention in the note are **correct**, but the link label "Theorem 2" on line 24 is **wrong** (see Major M1). I did not see the typeset IMRN version; its numbering should be confirmed when the citation is fixed.
- **Ghidelli (doi 10.1112/jlms.12312; arXiv 1910.05070), Theorem 1.1.** For every diagonal cubic form $a_1x_1^3+a_2x_2^3+a_3x_3^3$ with positive coefficients, it gives gaps of length $K$ below $N$ for all $K<\kappa_F\sqrt{\log N}/(\log\log N)^2$, with variables in $\mathbb N$, zero allowed. The note's line 77 agrees, including the $(\log\log N)^2$ (not $^4$). The note's criterion uses *positive* cubes. The transfer is valid, because a run of non-values of the nonnegative form is a run of non-values of the positive form, but the note should say so (Minor m5).
- **Selberg–Delange and Landau** (Theorem 2, aggregate law). These are standard and correctly invoked; see m3 for a wording point.

## 2. C4: the extraordinary claims (lines 150–253)

I tried to break each step. None broke.

### 2.1 Lemma 5, the determinant estimate (lines 170–185)

- **Definition of $B$ (lines 172–175).** $l^2|a/q-h/l|=l\,|al-qh|/q$. With $L=al-qh$, $L\equiv al\pmod q$, $L\ne0$ exactly when $h/l\ne u$. The minimum exists and is $\ge1/q>0$. The value at $l=1$ gives $B\le\tfrac12$ for $q\ge2$, and $B(n)=1$ for integers. Swapping $(l,L)$ gives $B(a/q)=B(a^{-1}/q)$. **The infimum ranges over every fraction $h/l\ne u$, uniformly in $h$, with no restriction to convergents or special denominators.** This answers the brief's question: the bound holds for every rational $A/Q$.
- **Proof (lines 181–184).** The three cases $L=0$, $|L|\ge2|z|w$ and $0<|L|<2|z|w$ are exhaustive.
  - In the third case, $w=m+a^{-1}L/q$ gives $(w+Ld/c)/L=a^{-1}/q-h'/l'$ with $l'=|cL|$. The fraction $h'/l'$ need not be reduced, and the definition of $B$ allows that.
  - It differs from $a^{-1}/q$ because $L+zw\ne0$, which is exactly the hypothesis $h/l\ne v$. Hence $|w+Ld/c|\ge B(u)/(c^2|L|)$, and multiplying by $w|z|$ and using $|L|<2|z|w$ gives $B(u)/(2c^2)$.
  - The case $q=1$ works with inverse 0.
  - **(5) is correct.**
- **Independent test (mine, not in the repository).** I ran a brute-force minimisation of $B$ on 1487 random cases with $q\in[1,44]$ (including $q=1$), $|c|\le39$ and denominators of $z$ up to 11. There were no violations. The bound is **attained**: at $u=1/3$, $z=1/10$, $B(v)=|z|$ through the $L=0$ branch. So (5) cannot be improved by a constant factor in general.

### 2.2 Theorem 6, the doubling schedule $W$ and the clustered $W'$ (lines 189–219)

- **Coefficients.**
  - The CRT moduli $p^k$ and $\operatorname{rad}(b)\mu_k$ are coprime. The least positive solution is $\le p^k\operatorname{rad}(b)\mu_k$, so $0<c_k\le\operatorname{rad}(b)$.
  - $u_k$ is a unit at $p$, because $u_k\equiv\mu_kb^{2^k}$ with both factors prime to $p$. It is a unit at every prime of $b\mu_k$, because $u_k\equiv1$.
  - The essential normalisation is $u_kb^{-2^k}/\mu_k\equiv1\pmod{p^k}$ in $\mathbb Z_p$. It replaces the requirement $t\mid n_k$ of Phase 22 Theorem G, so $t\nmid2^k$ is harmless.
- **Exact shifted denominators (line 198).** For $2^k\le n<2^{k+1}$, the term at $k$ has the unique deepest pole $p^k$. Each $\ell_j$ appears once, with a numerator that is a unit modulo $\ell_j$. Integer fillers do not change denominators. So the denominator is exactly $D_k=p^k\prod_{j^2\le k}\ell_j$, and every prime $\ell\nmid b$ eventually divides it. ✓
- **Unshifted $q_k=D_kb^{m_k}$.** After multiplying by $D_kb^{m_k}$, every earlier term carries a factor $b$. The last term is $u_kD_k/(p^k\mu_k)$ for $W$, or $D_k$ for $W'$, and is prime to $b$. ✓
- **$z_k$ heights (line 200).**
  - $z_k=A\,D_k^2\,b^{2w_k}/(p^{k+1}\mu_{k+1}b^{w_{k+1}})$, with $0<A\ll_b p^{k+1}\mu_{k+1}b^{w_{k+1}}$.
  - Both heights have logarithm $O(k+\sqrt k\log k+w_k+w_{k+1})=o(2^k)$.
  - Iterating (5) gives $\log(1/B(U_k))\le O(1)+\sum_{i<k}O(\log H(z_i))$. That is $O(k^2)$ for $W$ and $O(w_k)=o(2^k)$ for $W'$. ✓
- **Quantifiers in $\mu\le2$ (lines 200–205).**
  - For *every* large $l$, the first $k$ with $2^k\ge4\log_bl$ has $2^k<8\log_bl$, $q_k\ge b^{2^k}\ge l^4>l$ (so $h/l\ne U_k$ automatically), and $B(U_k)=b^{-o(2^k)}=l^{-o(1)}$.
  - The tail is $\ll b^{-2^{k+1}}\le l^{-8}$.
  - Hence $|W-h/l|\ge l^{-2-o(1)}$ uniformly in $h$. This also proves irrationality. Dirichlet gives $\mu\ge2$. ✓
- **Pole retention in every degree (lines 207–213).** This is the new ingredient, and it is correct.
  - Reflected losses $h_i=K-k_i\ge0$ range over the upward-closed set $U$. It contains the anchor $(\lceil\log_2r\rceil,\ldots)$, since $r\,2^{-\lceil\log_2 r\rceil}\le1$.
  - Dickson's lemma gives finitely many minimal vectors. Inclusion–exclusion gives $\sum_U x^{|\mathbf h|}=F(x)/(1-x)^r$ with $F(1)=\sum_{\emptyset\ne S}(-1)^{|S|+1}=1$. So $F(p)\equiv1\pmod{p-1}$, and $F(p)\ne0$ for $p\ge3$. The evaluation is valid in $\mathbb Z_p$ because $1-p$ is a unit.
  - Uniformity: the zero sets $Z_L$ are clopen and decreasing in the compact space of anchored upper sets, and their intersection is empty. So some $Z_L$ is empty, which gives the uniform $L(r,p)$.
  - For $K\ge2L$, every index with $|\mathbf h|<L$ is $\ge L+1$, so its unit is $\equiv1\pmod{p^L}$. Filler tuples and lower degrees have depth $\le(r-1)K$.
  - **Overlapping positions** (brief): positions of $W^r$ coincide, for example $2^a+2^a=2^{a+1}$, and positions of different degrees in $P$ coincide too. This is harmless. The argument evaluates the *entire* normalised prefix as one upper-set sum, so coincident tuples are already summed. Lower degrees are divisible by $p^{K}$ after normalisation.
  - So the $p$-exponent is $rK+O_P(1)$ at **every** late shift, with no exceptional set. ✓
- **Digit transfer (lines 215–219).**
  - Positions number $O((\log N)^r)$. Retained runs have length $\ge N^{1/3}$ and start at or above $\sqrt N$, so $K_0\ge\tfrac12\log_2N$ and $e\in[c_1\log N,c_2\log N]$.
  - $Q\mid D'\prod_{j^2\le K}\ell_j^r=N^{o(1)}$, so $\tau=N^{o(1)}$ and $M_0\ge N^{1/3-o(1)}$. $A(G)=a_0+v_p(\operatorname{ord}_Qb)=o(\log N)$, and Lemma A applies with a fixed $\theta$.
  - Erdős–Turán up to $N^\xi$ keeps a pole $\ge e-\xi\log_pN$.
  - **Short runs** (brief): runs shorter than $N^{1/3}$ are discarded and cost $O((\log N)^rN^{1/3})$, a power saving for $W$. For $W'$ the cluster windows cost $O(K^r2^{K-\sqrt K})=o(N)$, not a power saving. This is consistent with the note, which claims the power rate only for $W$.
  - Transcendence follows from normality of every nonconstant $P$. ✓

### 2.3 Theorem 7, the positive series $V$ with ratios tending to 1 (lines 221–250)

- **Counting (lines 225–229).**
  - The complete preceding shell gives $\gg2^k/\sqrt k$ positions. Since $h_i\ge\sqrt i/2$, splitting the sum $\sum_{i\le k}2^i/h_i$ at $k/2$ gives the matching upper bound $O(2^k/\sqrt k)$.
  - So $j\asymp n/\sqrt{\log n}$, which is $n_j\asymp j\sqrt{\log j}$. Gaps are $\le h_k\le\sqrt k$, so $n_{j+1}/n_j\to1$. ✓
- **Regrouping (lines 230–234).** $h_k$ is a power of two at most $\sqrt k<2^k$, so $h_k\mid2^k$. The geometric sum is exact, and $d_k=c_k+\lambda_k-\lambda_{k-1}$. The sums per shell are finite and the series converges absolutely.
  - $d_k$ can be negative: for $b=2$, $\lambda_3-\lambda_4=2/3$, while $c_4$ may be smaller. The note correctly says "signed". The raw $V$ is positive. ✓
- **The real danger: short runs at $n_j\asymp j\sqrt{\log j}$** (brief). Raw runs have length $\le h_K=O(\sqrt{\log N})$, far below any orbit estimate. **The proof never uses them.**
  - $\{b^nP(V)\}$ is a property of the real number. The proof computes it from the regrouped expansion, whose positions are the doubling positions, $O((\log N)^r)$ of them. The signed regrouped tail is $O(N^{-1})$ off buffers, and a uniform perturbation of size $\epsilon$ changes discrepancy by at most $2\epsilon$.
  - The periodic filler becomes the factor $1/(b^{h_k}-1)$. Its period $h_K$ divides the stride $\tau$, so Corollary B's splitting removes it.
  - The note states this distinction explicitly at line 235. ✓
- **$p$-adic control (line 237).**
  - $b^{h_k}-1$ has $p$-part $p^{a_0}$ or $1$: by LTE, $t\mid h_k$ forces $h_k/t$ to be a power of 2, and $p$ is odd.
  - Hence the normalised unit is $\equiv1\pmod{p^{i-a_0}}$. Tuples containing an early index lose depth $K-O(1)$. $K\ge2L+a_0$ suffices.
  - Every complementary denominator divides the prime-to-$bp$ part of $((b^{h_K}-1)\prod\ell_j)^r$, because $h_{k-1}\mid h_k$. Its logarithm is $O(\sqrt K\log K)$. ✓
- **Exponent (lines 243–248).**
  - $E_kd_k\in\mathbb Z$, using $h_{k-1}\mid h_k$, and it is nonzero for $k>a_0$ by the exact depth $-k$.
  - The numerator is $\equiv A_k\pmod{b^{2^{k-1}}}$. Since $\log_2|A_k|<2^{k-1}$ eventually, the valuations at radix primes agree.
  - Hence $q_k/b^{2^k}$ has height $\exp(O(k+\sqrt k\log k))$, and so do $z_k$ and its numerator. So $\log(1/B)=O(k^2)$, $q_k\ge b^{2^k-O(k+\sqrt k\log k)}>l$, and the tail is $O(b^{-2^{k+1}})$, which gives $\mu(V)=2$. ✓
- **Raw prefixes (line 250).** For raw prefixes, $\log_bq=n_j+o(n_j)$ and the tail exponent is $n_{j+1}+O(1)$. So criterion (4) genuinely fails, while regrouping proves $\mu=2$. ✓

### 2.4 My independent finite checks of Theorems 6–7 (scratch code, not committed)

These are finite measurements only. I computed exact prefixes for $(b,p)=(2,3)$ up to $k=12$ ($q\approx2^{4124}$) and for $(10,7)$ up to $k=10$.

- **Partial quotients.**
  - $W$: $\log_2(\max\text{ partial quotient})\le13.64$ for $(2,3)$ and $\le14.60$ for $(10,7)$.
  - Regrouped $\widetilde V$: $\le10.70$ for $(2,3)$ and $\le11.86$ for $(10,7)$.
  - This is consistent with $\log(1/B)=O(k^2)\ll2^k$.
- **Convergent exponents.** The convergents of $\widetilde V_K$ with $2^{10}<q\le\operatorname{den}\widetilde V_{K-1}$ have $-\log|\cdot|/\log q\le2.315$ and $\le2.280$.
- **Raw versus regrouped.** The raw-prefix identity $\text{raw}=\widetilde U_K-\lambda_Kb^{-2^K}$ holds exactly.
- **Pole retention.** At every insertion of the late shell, the defect $rK-v_p(\mathrm{den})$ of the regrouped prefix of $\widetilde V^r$ is at most 3 ($r=2$) and 7 ($r=3$) for $(2,3)$ with $K=11$, and at most 2 and 5 for $(10,7)$ with $K=8$. The prime-to-$bp$ part always divides $((b^{h_K}-1)\prod\ell_j)^r$.

### 2.5 Proposition 4 (lines 150–166)

- The gate $g_k\ge x$ is exactly $\xi-U_k\le1/(2Qq_k)$.
- Criterion (4) and its converse are correct, including uniformity across early terms and the choice $\log_bQ\ge\sqrt{n_k}$.
- $\max(\Lambda,1+\Lambda/(\Lambda-1))$ is minimised where $\Lambda^2-3\Lambda+1=0$, at $\Lambda=(3+\sqrt5)/2$, and geometric positions attain it.
- Both examples check out:
  - The positions $2^j,2^j+1$ satisfy (4), with ratio $\approx\tfrac12$.
  - The intervals $[a_j,a_j^2]$ fail it, with preceding gap $a_j/2$ at $a_j^2$.

  ✓

## 3. C1 (lines 16–55, summary line 9)

- **Theorem 1 (lines 18–24): correct.**
  - At shift $tM$, the prefix denominator divides $p^{2s\lfloor\log_p\sqrt M\rfloor}\le M^s$.
  - Suppose $C_s(2)^2=A/Q$. The tail $b^{tM}A/Q-b^{tM}\mathrm{Pre}$ is a positive rational with denominator dividing $\operatorname{lcm}(Q,p^e)\le QM^s$. This holds for **every** $Q$, including $Q$ sharing primes with $p$ or $b$ (brief).
  - $c(m)\le r_2(m)\le4\tau(m)$, and $M+g\ll M$.
  - With $g\ge(390/449-o(1))\log M$, we need $t\log b\cdot390/449\le s+\epsilon+o(1)$, which contradicts the hypothesis.
  - For $s=1$: $b^t\ge p+1\ge4$ and $(390/449)\log4\approx1.204>1$. The midpoint-rule bound $\log2\ge2/3$ is valid because $1/x$ is convex.
  - Theorem 1 does not use the split into $X_H$ and $Z_H$, so cancellation between $X_H$ and $Z_H$ (brief) is irrelevant here. In Theorem 2 and (A), $X_H$ has an integral shifted prefix, so $Z_H$ carries the whole fractional phase.
- **Theorem 2 (lines 28–37): correct.**
  - Since $p\nmid n$, every representation has $u\le k$. For $u<k$, both coordinates are units of equal valuation, and the level $2u\le2k-2\le H$ retires. This case is empty for $p\equiv3\pmod4$.
  - For $u=k$, $(n/p)=-1$ forces units.
  - The count is $r_2(n)/4=2^{\omega_1(n)}$, since a squarefree $n>1$ is not a square; $n=2$ checks.
  - Selberg–Delange with $z^{\omega_1}$, together with its Legendre twist (both twisted characters are nonprincipal, so the zeta exponent is 0), gives equidistribution of $\omega_1\bmod a$ on $F$.
  - $j\mapsto2^j/D\bmod1$ is injective on $\mathbb Z/a$.
- **Aggregate law (A) (lines 41–55): correct.**
  - In the Landau differencing over finitely many fixed normalised cells, the cell lengths scale with $Y$ and the $O(X/\log^{3/2}X)$ remainder is uniform.
  - In relative density, the arrivals are frozen with $e_i\ge s\log_pY-O_{H,L}(1)$.
  - Starts with long spans are rare: at most $MY^{1-\delta}$.
  - Positions with innovation pole $\ge\delta\log_pY$ number $O(Y^{1-\delta/s}\log Y\,p^{-H})$.
  - LTE gives exactly $e_i-v_p(b^t-1)-v_p(\Delta)\ge(s-2\delta-o(1))\log_pY>\delta\log_pY$. ✓

## 4. C2 (lines 57–85, summary line 10)

- **Packet lemma (lines 63–67): correct.** $R_{n+j}=b^jR_n+V_j$ and $T_{n+j}=b^jT_n-V_j$. Replacing the unit numerator preserves the exact denominator $p^e$. Units are spaced at most $2/q$ apart because $p\ge3$. A cylinder of length $b^{-B}\ge2/q$ therefore contains a grid point.
- **Eligible starts (line 69): correct.** Phase 21 Proposition D with $d=r$ gives $rsJ=s\log_pN+O(1)$. For a fixed vector of losses, there are $O(Np^{-h})$ tuples through $2N$ when $r=d$. The total charge is $O(BN^{1-\beta'/s}(\log N)^{r-1})=o(N)$.
- **Cubic (lines 71–75): correct.**
  - Modulo 9: cubes lie in $\{0,\pm1\}$, so $\pm4$ is impossible, $\pm3$ needs three units of the same sign, and $\pm2$ has exactly one zero slot (giving the factor 3 by permuting slots).
  - At $3^{3a+1}$: AM–GM is strict except on the diagonal, and the other triples fall into 3-cycles. Hence $3^{3a-H}z_H\equiv1\pmod9$.
- **Conditional criterion (line 77): correct.** For $j^3+k^3=B$, the divisor $j+k\mid B$ fixes $jk$. The threshold is $(4/3)/(2\log2)=2/(3\log2)\approx0.962$. The Ghidelli bound is stated accurately and is correctly called insufficient.
- **Concentration form (lines 79–83): correct.** An interval with discrepancy $>1-\min(\epsilon,\eta)$ either is shorter than $\epsilon$ and holds more than $(1-\eta)N$ points, or has a complement with that property.
- **Scope.** The barrier concerns hypothetical continuations, and the note says so (line 85). The evidence label is appropriate.

## 5. C3 (lines 87–148, summary line 11)

- **Freezing (lines 95–99): correct.**
  - Lower weighted degrees carry $p^{(S-s\cdot\nu)J}$, which needs $J\ge L$ for a weight gap of one.
  - Surviving tuples have $h<L/s_1$ and $d(J-h)>L$.
  - A single linear maximiser has residue $\lfloor u^{1/d}\rfloor\in[1,p-1]$.
  - The script's fixture (lines 239–244) shows that the Phase 21 Theorem M threshold $J\ge\lceil L/s_1+L/d\rceil$ alone is **insufficient** when there is a weight gap of one. At $L=2$, $J=1$, $u=1$, the residue is $1+p$ instead of $1$. This is harmless for qualitative normality, where $L$ is fixed and $J\to\infty$, but it is an unrecorded erratum to Phase 21 (m6).
- **Tie structure and centre (lines 105–110).**
  - Lexicographic minimality implies entries $\ge s_*$, at most $l$ copies of $s_*$, and no proper prefixes, since all lists in a tie have the same weighted sum.
  - Remaining unweighted loss is $<7h/6+O(1)<3h/2$.
  - The fine coordinate has order $s_*$ once $\kappa<1/(s_m+2)$.
  - A degree-one competitor in a nonlinear tie has order $>s_*$. Its cost is $p^{(\kappa+s_*/(s_*+1))H}$, valid with $\kappa<1/(2(s_*+1))$.
  - The jump multiplicity is $\prod_a\nu_{*,a}!$, and the precision $\pi_H$ is correct.
- **Weighted isolation estimate (lines 112–130).**
  - Step 1, peeling, follows Theorem M with the divisor bound. The saving is $p^{h/3}$ when the divisor-bound exponent is $\le1/(6d)$.
  - Step 3 bounds the sum of $p^{H'}$ over admissible losses by $O(V)$ through a convergent product over higher orders. This correctly accounts for every lower multiplicity $j_0$.
  - Step 4 is the genuine improvement over Theorem M's $L^1$ Lebesgue-point localisation. A regular competitor varies a coordinate of loss $\ge H/(2r)$ and size $\ge\tau'$, so the derivative lower bound $d\tau'^{d-1}$ is unaffected by translations from fixed higher-order slots. Irregular competitors are counted globally with weight $\tau'$. This disposes of the singular densities that forced Lebesgue points in Phase 21.
  - Step 2 imports the GF-11/Lemma I row margins. I checked that the substitutions $H'\le H+C$, $v'\ge H'/r$ and $q\le r+1\le d$ keep those margins' hypotheses. I did **not** re-derive the Titchmarsh 5.13 exponents (line 126).
  - The iteration (line 132) mirrors Theorem Q exactly.
- **Digits and the hybrid budget (lines 136–148): correct.**
  - The cell count is $o(N^{r/d})$.
  - $A(G)=a_0+v_p(\operatorname{ord}_Qb)=O(\log N/\log\log N)$ by Phase 22 Lemma D. The lemma applies because the $\ell_j$ form an initial segment of the primes away from $bp$ and $\operatorname{ord}_\Lambda b\le N$.
  - Lifting by $D'$ costs a fixed factor.
  - The exact order is $\operatorname{ord}_{\Lambda^r}b=\operatorname{lcm}(A_b,E)$ for odd squarefree $\Lambda$. I checked this prime by prime: at $\ell_0\mid\Lambda$, $v_{\ell_0}(\operatorname{ord}_{\ell_0}b)=0$.
  - The $r\ge2$ and $r=1$ insertion scales agree with the Phase 22 table.

## 6. Script audit

- `certified_bits` (lines 157–169) is sound. The omitted tail is $<2^{-\text{precision}}$, and the floor at both ends of the enclosing interval certifies the word.
- `check_jumps` independently enumerates ordered representations, including all retired levels.
- `check_actual_packets` checks the recurrence and (A) exactly, with $s=1$ implicit.
- **Tautological assertions** (lines 421–422 and 451–452). `z / previous_q**2 == new_coeff / b**n` and `previous + z/previous.denominator**2 == current` hold by construction. They do not test the height bound on $z_k$, which is what the proof needs (m9).
- **Lemma 5 coverage** (line 331). The test uses $q\in[2,16]$ and $|c|\le5$, and omits $q=1$, although the lemma claims that case (m9).
- **Theorem 7 pole retention** is checked through the normalised units (line 420) and the raw denominators. It is not checked by a direct convolution of $\widetilde V^r$ against the reflected residue. My check in §2.4 supplies this as a finite measurement (m9).

## 7. Findings

| # | Severity | Location | Finding | Fix |
|---|---|---|---|---|
| **M1** | **Major** | line 24 | The external-input link says "**Theorem 2**" of DEKKM. In the five-author accepted manuscript, $390/449$ is **Theorem 1**. Theorem 2 (general $D$) gives only $\approx0.2215$ at $D=-4$, and $0.2215\cdot\log4\approx0.31<1$, so following the stated pointer does **not** prove Theorem 1, even for $s=1$. The mathematics is unaffected. | Change to "Theorem 1" (confirm against the typeset IMRN numbering). State that $s_n$ counts positive integers, zero coordinates allowed, with the natural log. |
| m1 | Minor | line 26 | "The integer part $X_H$" is a misnomer: $X_H$ is the series with integral coefficients. "In the question" is leftover prompt wording. | Reword both. |
| m2 | Minor | line 9 and line 259 | The finite residue histograms are far from the uniform limit law; for $p=5$ they are $(1,30,1,0)$ on four residues. This is expected, since convergence in $\omega_1$ happens at scale $\log\log Y$, but the note is silent. | Add one sentence saying these counts are not evidence for the limiting law. |
| m3 | Minor | line 37 | "A factor analytic near 1" understates what Selberg–Delange needs. The residual Euler factor converges absolutely for $\Re u>1/2$. Here $u$ clashes with the normalised position $u$. | Say "absolutely convergent for $\Re>1/2$" and rename the variable. |
| m4 | Minor | line 258 | $s=1$ is implicit in the finite packet measurement. | State $s=1$. |
| m5 | Minor | line 77 | Ghidelli's theorem concerns *nonnegative* cubes, while the criterion uses positive cubes. | Add the one-line transfer: non-values of the nonnegative form are non-values of the positive form. |
| m6 | Minor | lines 95–99 | The condition $J\ge L$ corrects the freezing display of Phase 21 Theorem M (multivariate note, lines 26–30), and the script demonstrates this (lines 239–244). The note does not record it as an erratum. | Add an explicit erratum sentence. It is harmless for qualitative Theorem M and needed for the effective rate. |
| m7 | Minor | lines 101–132 | Theorem 3's proof is a dense adaptation. The constant order $(c,\kappa,\lambda,\mu,\epsilon_0,A,H_*)$ is scattered, and step 2 relies on unstated GF-11 parameters. | Before manuscript use, state a multivariate Lemma I with explicit parameter dependencies, as Phase 21 did for Lemma I. |
| m8 | Minor | throughout | Notation overload: $\mu$ is the irrationality exponent, the isolation exponent and the auxiliary denominator. $\epsilon$ is the isolation radius and the divisor exponent. $d$ is the degree and the denominator of $z$ in Lemma 5. $A_b$ is $\operatorname{ord}_\Lambda b$ (line 148) and Lemma D's lcm (same paragraph). $u$ is a position and the Dirichlet variable. | Rename locally. |
| m9 | Minor | script lines 331, 421–422, 451–452 | Vacuous $z_k$ assertions. Lemma 5 is untested at $q=1$ and for larger $c$. There is no direct convolution test for Theorem 7. | Assert height bounds for $z_k$. Compute the maximum partial quotient of $U_k$ (it equals $1/B$ up to a factor $\le3$). Extend the Lemma 5 grid. Add a $\widetilde V^r$ convolution test. |
| m10 | Minor | lines 189–219 | The relationship to Phase 22 Theorem S is unstated. Theorem S has the Stoneham schedule and $\mu=p\ge3$, and truncation separation gives only $\max(2,3)=3$ at ratio 2. | Add a sentence: the twisted numerators replace $t\mid n_k$, the upper-set lemma replaces the Phase 13/14 periodic-mass input, and Lemma 5 replaces truncation separation. |
| m11 | Minor | line 219 | "As in §4" leaves the run parameters implicit: $K_0\ge\tfrac12\log_2N$, $\theta$, $\xi$, and $M_0\ge N^{1/3-o(1)}$. | Spell them out in two lines. |
| m12 | Minor | line 12 | The phrase "optimal universal ceiling certificate bounded below by" is garbled. | Write: "the best exponent certifiable by distinct-prefix truncation separation is at least $(3+\sqrt5)/2$ for every schedule, with equality at geometric ratio $(3+\sqrt5)/2$." |
| m13 | Minor | line 185 | The determinant estimate (5) resembles the classical continued-fraction folding for $\sum u^{-2^k}$, to which line 185 alludes. | Add a literature pointer (I did not verify a specific reference). |

## 8. Verdicts

- **C1: ACCEPT AFTER REVISION.** Theorem 1 is correct, with the correct constant and authors, but the external-input pointer must name DEKKM **Theorem 1** (M1). Theorem 2 and the aggregate law (A) are correct as paper proofs. Address m1–m4.
- **C2: ACCEPT AFTER REVISION.** The packet barrier, the density of eligible starts, the exact cubic structure modulo 9 and both conditional statements are correct. The scope caveats are accurate. Address m5.
- **C3: ACCEPT AFTER REVISION.** I found no mathematical error. Step 4 legitimately replaces the Lebesgue-point step, and the hybrid budget is correct with Lemma D. The proof is too compressed for an unaided check of step 2's imported exponents. Record the Phase 21 freezing erratum (m6) and expand the exposition (m7, m8).
- **C4: ACCEPT AFTER REVISION.** The extraordinary claims survive maximal hostility, with no counterexample, gap or hidden hypothesis found. Lemma 5 holds for every rational $A/Q$. The upper-set lemma gives exact pole retention at every late shift in every degree. The dense raw support of $V$ never enters the digit argument, because the regrouped expansion carries it. $\mu(W)=\mu(W')=\mu(V)=2$ follows from the height bounds. The revisions are expository and concern the script (m9–m13).

*Cross-model review is not independent human peer review. The script's exact checks and my independent computations are finite measurements or finite certificates. They do not prove the asymptotic theorems; those rest on the paper proofs audited above.*

---

## Post-Repair Verification

**Reviewer:** `claude-opus-5-5`. **Re-audited (read-only):** `notes/phase23/nonlinear-multivariate-and-denser-mu.md` (blob `23050f7e`) and `scripts/phase23_nonlinear_short_orbits.py` (blob `b895098f`). Line numbers below refer to these blobs. I modified neither file and committed nothing.

**Reproduction.** `python -B scripts/phase23_nonlinear_short_orbits.py` exited **0** in about 1.7 s (Windows, Python 3.13) and printed `All exact checks passed.` Every number in §9 (lines 258–262) matches the output: 643 / 479 / 164 arrivals; 1871 / 1200 / 427 packets; residue counts `(1:9, 2:29)` and `(1:1, 2:30, 4:1)`; 1044 ones / 1023 changes and 983 / 1100 over denominator 2047; 32 words at q = 81; residues `2, 41, 15, 15, 60 mod 81`; **1960** determinant-lemma corrections; 251 antichains; shifted prefix denominators through shift 1023 (`range(1, 2**10)`) in three radices. The count 1960 is `assert`ed and agrees with a hand count: 2·8·4 = 64 cases at q = 1, plus 24 · Σ_{q=2}^{16} φ(q) = 24 · 79 = 1896.

| Item | Status | Evidence |
|---|---|---|
| **M1** | **Closed** | Line 24 now links "Theorem 1 (accepted manuscript)". It states the result for positive integers that are sums of two squares, with zero coordinates allowed and the natural logarithm. It keeps the constant 390/449 and the margin check log 4 > 449/390. This is the theorem that proves the result, so the evidence pointer is now sufficient. |
| m1 | Closed | Line 26 reads "integral-coefficient series X_H". The phrases "integer part" and "in the question" no longer appear. |
| m2 | Closed | Line 259 says the histograms are far from the uniform limit law (convergence at scale log log Y) and are not evidence for it. |
| m3 | Closed | Line 37 says the residual Euler factor converges absolutely for Re σ > 1/2, and the Dirichlet variable is renamed σ. |
| m4 | Closed | Line 258 states s = 1. |
| m5 | Closed | Line 77 adds the transfer from nonnegative to positive cubes. |
| m6 | Closed | Lines 97–99 add J ≥ L to the freezing condition and include an explicit erratum to Phase 21 Theorem M that cites the L = 2, J = 1, u = 1 fixture (script lines 239–244). |
| m7 | Closed (as a deferral) | The parameter order (c, κ, λ, μ₀, A, H_*, ε₀) is stated in one place (line 112). Line 120 records that the GF-11 / Lemma I margins carry over under H′ ≤ H + C, v′ ≥ H′/r, q ≤ r + 1 ≤ d. It also says a standalone multivariate Lemma I is required before manuscript use, which is what m7 asked for. |
| m8 | Closed (residual nit) | Several symbols are renamed: the isolation exponent is μ₀, the divisor exponent ε_div, the Lemma 5 denominator d_z, ord_Λ b is O_Λ (line 148), and the Dirichlet variable σ. Three minor clashes remain, none ambiguous in context. First, the auxiliary denominators μ_i, μ_k appear next to μ(·) and μ₀. Second, M₀ denotes both the integer in step 1 (line 122) and the block count (lines 146, 219). Third, σ is both the Dirichlet variable (§1) and the margin in (3) (§4). Renaming them is optional. |
| m9 | Closed | The four script gaps from §6 are fixed. **(i) Height bounds.** The tautological z-identities are replaced by explicit bounds on the numerator and denominator of z_k, with no b^{2^k} factor: lines 513–517 for W and W′, and 443–448 for the regrouped Ṽ. **(ii) Lemma 5 at q = 1.** It is now tested at q = 1 (u = 0, 1, with \|c\| ≤ 11), and at q ∈ [2, 16] with \|c\| ≤ 7 (lines 344–363). **(iii) Partial quotients.** The maximum partial quotient is asserted to be below 2^16 for W, W′ (line 519) and for Ṽ in all three radices (line 452). **(iv) Convolutions.** Ṽ² and Ṽ³ are convolved directly at the late shell K = 8 (lines 453–486). The test asserts pole defect ≤ 8 and that the complementary denominator divides ((b^{h_K} − 1) ∏ ℓ_j)^r. *Nit:* the convolution test checks only the shell-end prefix, with a generous allowance of 8. I checked every insertion prefix in the shell 256 ≤ n ≤ 511 myself (scratch code, not committed). The maximum defects are 3 and 7 for (b, p) = (2, 3) and (4, 3), and 2 and 5 for (6, 5). They are within the allowance and agree with §2.4. |
| m10 | Closed | Line 194 compares the construction with Phase 22 Theorem S: twisted CRT numerators replace t ∣ n_k, the anchored upper-set lemma replaces the Phase 13/14 input, and Lemma 5 replaces truncation separation (which certifies at best 3 at ratio 2). |
| m11 | Closed | Line 219 states the run parameters: K₀ ≥ ½ log₂ N, T′ ≥ N^{1/3}, τ = N^{o(1)}, M₀ ≥ N^{1/3 − o(1)}, a principal-unit valuation of o(log N), a fixed small ξ with c₁ log N ≤ e ≤ c₂ log N, and a fixed θ with p^{θe} ≤ M₀. |
| m12 | Closed | Line 12 uses the wording "best exponent certifiable by distinct-prefix truncation separation is at least (3+√5)/2 … with equality at geometric ratio (3+√5)/2". |
| m13 | Closed | Line 185 cites the folding lemma of Shallit (1979) and van der Poorten–Shallit (1992). These are the standard references for folded continued fractions of Σ u^{−2^k}. I did not re-read the sources for this check. |

**Regression check.** The repairs leave the mathematics of §§1–8 as audited above. The new text (the erratum, comparison and parameter sentences) introduces no new claim. The §9 descriptions match what the script actually asserts.

**Final verdict: ACCEPT** for C1, C2, C3 and C4. M1 and m1–m13 are cleanly closed. The m8 and m9 nits above are optional and do not block acceptance. The evidence labels stand. Theorems 1–7, Proposition 4, Lemma 5 and the aggregate law (A) are **Paper proofs**; Theorem 1 additionally depends on the cited DEKKM theorem as **External input**. The §9 items are finite measurements or finite certificates only. The cubic irrationality criterion and the packet-discrepancy statement remain **Conditional**, and the items in the two Open paragraphs remain **Open**.

*Cross-model review is not independent human peer review.*
