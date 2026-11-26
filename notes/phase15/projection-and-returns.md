# Higher-rank Fredholm projections, solenoids, and induced-return equivalences

Every fixed-width approximant described below is binary normal and shadows ln 2 with an explicit real error. The normality assertion fixes the width before taking the orbit limit. Inducing on binary transitions gives a different test directly on the true orbit, in which the time already spent in an unfinished run must be counted. These are paper results. The [finite checks](../../scripts/phase15_projection.py) use exact rational arithmetic for residues and digit counts and numerical arithmetic for logarithms and trigonometric functions.

## 1. Higher-rank Fredholm identities and convergence

Let $P = \{p_1, \dots, p_r\}$ be a nonempty finite set of distinct primes. Write
$$
S = \langle P \rangle = \left\{p_1^{a_1}\cdots p_r^{a_r} : a_i \in \mathbb{Z}_{\ge 0}\right\},
\qquad
U_P = \left\{d \in \mathbb{Z}_{\ge 1} : \gcd\!\left(d, \prod_{p\in P} p\right) = 1\right\}.
$$
For $D \subseteq P$, abbreviate $D = \prod_{p \in D} p$ (with $\emptyset \mapsto 1$) and $\mu(D) = (-1)^{|D|}$. Let $w : \mathbb{N} \to \mathbb{C}$ be completely multiplicative, and on $\mathcal{O}_0(\mathbb{D}) = \{F \in \mathcal{O}(\mathbb{D}) : F(0) = 0\}$ define the commuting weighted substitution operators $(M_{p,w} F)(z) = w(p) F(z^p)$ and the rank-$r$ mixed-difference operator
$$
\Delta_{P,w} := \prod_{p \in P} (I - M_{p,w}) = \sum_{D \subseteq P} \mu(D)\, w(D)\, T_D,
\qquad (T_D F)(z) := F(z^D).
$$

### Theorem 1.1 (Higher-rank box telescoping and uniform convergence)
Let $F \in \mathcal{O}_0(\mathbb{D})$ and let $w(p_1), \dots, w(p_r) \in \mathbb{C}$ be arbitrary.

1. **Exact finite-box identity.** For every box $A = (A_1, \dots, A_r) \in \mathbb{Z}_{\ge 1}^r$ and every $z \in \mathbb{D}$,
   ```math
   F(z) - \sum_{\substack{0 \le a_j < A_j \\ 1 \le j \le r}}
   w(p_1^{a_1}\cdots p_r^{a_r})\, (\Delta_{P,w} F)\!\left(z^{p_1^{a_1}\cdots p_r^{a_r}}\right)
   = \sum_{\emptyset \ne J \subseteq \{1,\dots,r\}} (-1)^{|J|-1}
   \left(\prod_{j \in J} M_{p_j, w}^{A_j} F\right)(z).
   ```
2. **Doubly-exponential uniform convergence.** For any $0 < \rho < 1$, put $C_\rho = \sup_{|u|=\rho} |F(u)|/\rho < \infty$ (for $\operatorname{Li}_s$ with $\operatorname{Re} s \ge 0$, $C_\rho \le (1-\rho)^{-1}$). On $|z| \le \rho$, the remainder has modulus at most
   ```math
   C_\rho \sum_{\emptyset \ne J \subseteq \{1,\dots,r\}}
   \left(\prod_{j \in J} |w(p_j)|^{A_j}\right) \rho^{\prod_{j \in J} p_j^{A_j}}
   \longrightarrow 0 \qquad (\min_{1 \le j \le r} A_j \to \infty).
   ```
   Consequently, $F(z) = \sum_{m \in S} w(m)\,(\Delta_{P,w} F)(z^m)$ converges absolutely and uniformly on every compact subset of $\mathbb{D}$.

**Proof.** Because $M_j := M_{p_j,w}$ commute pairwise, the finite geometric factorizations $I - M_j^{A_j} = (I - M_j)\sum_{a_j=0}^{A_j-1} M_j^{a_j}$ multiply to
$$
\left(\sum_{0 \le a_1 < A_1} \cdots \sum_{0 \le a_r < A_r} M_1^{a_1}\cdots M_r^{a_r}\right)\Delta_{P,w}
= \prod_{j=1}^r (I - M_j^{A_j})
= I - \sum_{\emptyset \ne J \subseteq \{1,\dots,r\}} (-1)^{|J|-1}\prod_{j\in J} M_j^{A_j}.
$$
Applying both sides to $F$ yields (1). By the Schwarz lemma on $|u| \le \rho$, $|F(u)| \le C_\rho |u|$ for all $|u| \le \rho$. Since $|z^{p_j^{A_j}}| \le \rho^{p_j^{A_j}} \le \rho$, each boundary term satisfies $|(\prod_{j \in J} M_j^{A_j} F)(z)| \le C_\rho (\prod_{j\in J} |w(p_j)|^{A_j}) \rho^{\prod_{j\in J} p_j^{A_j}}$. Because $p_j \ge 2$ and $\rho < 1$, the doubly-exponential factor $\rho^{p_j^{A_j}}$ dominates any exponential factor $|w(p_j)|^{A_j}$, proving uniform convergence of the box sums. For absolute convergence of $\sum_{m \in S} |w(m)|\,|(\Delta_{P,w} F)(z^m)|$ on $|z| \le \rho$, observe that $\Delta_{P,w} F \in \mathcal{O}_0(\mathbb{D})$ satisfies $|(\Delta_{P,w} F)(z^m)| \le C'_\rho \rho^m$; writing $m = \prod_{j=1}^r p_j^{a_j}$ and using $m \ge \frac{1}{r}\sum_{j=1}^r p_j^{a_j}$ (AM–GM/max bound), $\sum_{m\in S} |w(m)|\rho^m \le \prod_{j=1}^r \sum_{a_j=0}^\infty |w(p_j)|^{a_j} \rho^{p_j^{a_j}/r} < \infty$. $\square$

### Theorem 1.2 (Higher-rank Fredholm series and boundary dichotomy)
For $s \in \mathbb{C}$, define the weighted higher-rank Fredholm series (localized polylogarithm)
$$
\Phi_{P,s}(z) := \sum_{m \in S} \frac{z^m}{m^s} \qquad (|z| < 1).
$$
At $s = 0$ and $P = \{2\}$, $\Phi_{\{2\},0}(z) = \sum_{k=0}^\infty z^{2^k}$ is the classical Fredholm series (whose value at $z = 1/2$ is the Fredholm–Kempner constant $K$).

1. **Functional equation.** With $w(m) = m^{-s}$, $\Delta_{P,w} \Phi_{P,s}(z) = z$ identically on $\mathbb{D}$.
2. **Closed-disk convergence for $\operatorname{Re} s > 0$.** Whenever $\sigma = \operatorname{Re} s > 0$,
   $$
   \sum_{m \in S} |m^{-s}| = \prod_{p \in P} \frac{1}{1 - p^{-\sigma}} < \infty,
   $$
   so $\Phi_{P,s}$ converges absolutely and uniformly on the closed disk $\overline{\mathbb{D}}$ and belongs to the Wiener algebra $A(\mathbb{T})$.
3. **Natural boundary.** For every complex $s$, $\Phi_{P,s}$ has radius of convergence $1$ and the unit circle $\partial\mathbb{D}$ is a natural boundary.

**Proof.** For (1), the coefficient of $z^m$ ($m \in S$) in $\Delta_{P,w}\Phi_{P,s}(z)$ is $m^{-s} \sum_{D \subseteq D(m)} (-1)^{|D|}$, where $D(m) = \{p \in P : p \mid m\}$; this equals $1$ if $D(m) = \emptyset$ (i.e. $m = 1$) and $0$ otherwise. For (2), unique factorization in $S = \langle P \rangle$ factors the positive series into a finite product of convergent geometric series.

For (3), the support through $X$ has size at most $\prod_{p\in P}(1+\lfloor\log_p X\rfloor)$. Thus its increasing enumeration $m_j$ satisfies $m_j/j\to\infty$. The nonzero coefficients have $|m_j^{-s}|^{1/m_j}\to1$. Fabry's gap theorem gives a natural boundary for every fixed complex $s$, including the absolutely convergent boundary series when $\Re s>0$. This concerns holomorphic continuation across an arc. [Fabry gap theorem and density formulation](https://www.math.purdue.edu/~eremenko/dvi/fabry4.pdf)

### Theorem 1.3 (Polylogarithm Euler–Fredholm factorization)
Let $P$ be a finite set of distinct primes, $S = \langle P \rangle$, $U_P = \{d \ge 1 : \gcd(d, \prod P) = 1\}$, and $s \in \mathbb{C}$. For all $|z| < 1$,
```math
\operatorname{Li}_s(z)
= \sum_{n=1}^\infty \frac{z^n}{n^s}
= \sum_{d \in U_P} \frac{1}{d^s}\, \Phi_{P,s}(z^d)
= \sum_{m \in S} \frac{1}{m^s}\, g_{P,s}(z^m),
```
where the rank-$r$ mixed difference is
```math
g_{P,s}(z) := (\Delta_{P,s}\operatorname{Li}_s)(z)
= \sum_{D \subseteq P} \frac{\mu(D)}{D^s}\, \operatorname{Li}_s(z^D)
= \sum_{d \in U_P} \frac{z^d}{d^s}.
```
Both iterated series converge absolutely and uniformly on compact subsets of $\mathbb{D}$.

**Proof.** Every $n \ge 1$ factors uniquely as $n = d m$ with $d \in U_P$ and $m \in S$, and $\sum_{d \in U_P} \sum_{m \in S} |z|^{dm} (dm)^{-\operatorname{Re} s} = \sum_{n=1}^\infty |z|^n n^{-\operatorname{Re} s} < \infty$ on $\mathbb{D}$, justifying both rearrangements by Tonelli–Fubini. Applying $\Delta_{P,s}$ termwise annihilates every $n$ divisible by some $p \in P$ and leaves $n \in U_P$ unchanged, giving $g_{P,s}$. $\square$

At $s = 1$ and $z = 1/2$, $\operatorname{Li}_1(1/2) = \ln 2$, and every mixed difference evaluates to a single rational multiple of the logarithm of an explicit rational number,
$$
g_{P,1}(1/2) = \frac{1}{L}\ln Q_P,
\qquad L = \prod_{p\in P} p,
\qquad Q_P = \prod_{D \subseteq P} (1 - 2^{-D})^{-\mu(D) L / D}.
$$
Verified exact evaluations in [`scripts/phase15_projection.py`](../../scripts/phase15_projection.py):

| Prime set $P$ | Rank $r$ | Exact mixed difference $g_{P,1}(1/2) = \sum_{\gcd(d,L)=1} 2^{-d}/d$ | Numerical value |
| --- | ---: | --- | ---: |
| $\{2\}$ | 1 | $\tfrac{1}{2}\ln 3$ | $0.549306144334$ |
| $\{3\}$ | 1 | $\tfrac{1}{3}\ln 7$ | $0.648636716352$ |
| $\{2, 3\}$ | 2 | $\tfrac{1}{6}\ln 21$ | $0.507420406287$ |
| $\{2, 3, 5\}$ | 3 | $\tfrac{1}{30}\ln\!\bigl(\tfrac{61862655771}{18271}\bigr)$ | $0.501170405094$ |

In particular, with $P=\{2,3,5\}$, unit weights and $F(w)=w$, let $L_{2,3,5}(w)=\sum_{i,j,k\ge0}w^{2^i3^j5^k}$. Successive cancellation of the positive $j,k$ exponents gives $(I-T_3)(I-T_5)L_{2,3,5}=L$ exactly. Applying $I-T_2$ gives $w$. By the [uniform binary radial comparison](fredholm-and-products.md), the difference of the real radial values of this *mixed difference* between angles zero and $2\pi x$ approximates the binary escape sum with error at most two. A leading term for $L_{2,3,5}$ alone supplies no corresponding estimate on this residual.

## 2. Mixed differences, finite-width projections, and the width-vs-horizon obstruction

Truncating the outer sum in Theorem 1.3 at $s = 1$, $z = 1/2$ to a finite width $W \ge 1$ defines the **finite-width projection**
```math
\Pi_{P,W}(1/2) := \sum_{\substack{d \in U_P \\ d \le W}} \frac{1}{d}\, \Phi_{P,1}(2^{-d})
= \sum_{n \in \mathcal{S}_{P,W}} \frac{1}{n \, 2^n},
\qquad
\mathcal{S}_{P,W} := \bigsqcup_{\substack{d \in U_P \\ d \le W}} d \cdot \langle P \rangle.
```
Write $\Pi_{P,W}^{(N)}(1/2) = \sum_{n \in \mathcal{S}_{P,W},\, n \le N} n^{-1} 2^{-n}$ for the binary-exponent truncation and $q_{P,W,N} = \operatorname{den}(2^N \Pi_{P,W}^{(N)}(1/2))$ for its reduced denominator. Set $D_{P,W} := \operatorname{lcm}\{d \in U_P : d \le W\}$ and $P_W := P \cup \{q \text{ prime} : q \le W\}$.

### Theorem 2.1 (Exact $3$-adic survival and binary normality of finite-width projections)
Let $P$ be any finite set of primes containing $3$, and let $W \ge 1$ be any integer width.

1. **Exponential approximation to $\ln 2$.**
   ```math
   0 < \ln 2 - \Pi_{P,W}(1/2) \le \frac{2^{-W}}{W + 1}.
   ```
2. **Zero-cancellation $3$-adic profile.** For every integer $N \ge 3$, $q_{P,W,N}$ divides $D_{P,W} \prod_{p \in P} p^{\lfloor\log_p N\rfloor} \le D_{P,W} N^{|P|}$, has prime support inside $P_W$, and satisfies the **exact** $3$-valuation identity
   ```math
   v_3(q_{P,W,N}) = \lfloor \log_3 N \rfloor.
   ```
3. **Full binary normality.** For every finite $P \ni 3$ and every finite $W \ge 1$, the number $\Pi_{P,W}(1/2)$ is normal in base $2$, i.e. $D_\infty(\Pi_{P,W}(1/2)) = 0$.

**Proof.**
*(1)* Every omitted integer $n \in \mathbb{N} \setminus \mathcal{S}_{P,W}$ has $P$-rough part $d > W$, hence $n \ge d \ge W + 1$. Thus $0 < \ln 2 - \Pi_{P,W}(1/2) \le \sum_{n = W+1}^\infty \frac{1}{n 2^n} \le \frac{1}{W+1}\sum_{n=W+1}^\infty 2^{-n} = \frac{2^{-W}}{W+1}$.

*(2)* Let $k = \lfloor \log_3 N \rfloor \ge 1$, so $3^k \le N < 3^{k+1}$. Every retained term $n = d m \in \mathcal{S}_{P,W}$ with $n \le N$ has $v_3(n) = v_3(m) \le k$, and $n \mid D_{P,W} \prod_{p\in P} p^{\lfloor\log_p N\rfloor}$. Which retained terms have $v_3(n) = k$? Write $n = 3^k m'$ with $3 \nmid m'$; since $n < 3^{k+1}$, necessarily $m' \in \{1, 2\}$. Now $m' = 1$ always lies in $\mathcal{S}_{P,W}$ (via $d = 1$, $m = 3^k$), and $m' = 2$ lies in $\mathcal{S}_{P,W}$ if and only if $2 \in P$ or $W \ge 2$.
- For $3^k \le N < 2 \cdot 3^k$, only $m' = 1$ appears with $v_3 = k$. Multiplying $2^N \Pi_{P,W}^{(N)}(1/2)$ by $3^k$ gives $2^{N - 3^k} \not\equiv 0 \pmod 3$.
- For $2 \cdot 3^k \le N < 3^{k+1}$, either only $m' = 1$ appears (if $2 \notin P$ and $W = 1$), or both $m' = 1, 2$ appear. In the latter case, the $3^k$-scaled residue modulo $3$ is
  $$
  2^{N - 3^k} + \frac{2^{N - 2 \cdot 3^k}}{2}
  = 2^{N - 2 \cdot 3^k - 1}\bigl(2^{3^k + 1} + 1\bigr).
  $$
  Because $3^k$ is odd, $3^k + 1$ is even, so $2^{3^k + 1} \equiv 1 \pmod 3$ and $2^{3^k + 1} + 1 \equiv 2 \not\equiv 0 \pmod 3$.

Hence $v_3(q_{P,W,N}) = k$ at every $N \ge 3$ with zero exceptions.

*(3)* For $P=\{3\}$ and $W=1$ this equals $1/2+\alpha_{2,3}$ under the usual Stoneham convention starting at $j=1$. The dyadic summand disappears after one shift. [Bailey–Crandall](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf) · [Vandehey and the fixed-support estimate](../../papers/04-arithmetic-certificates/references.bib)

Fix $P \ni 3$ and $W \ge 1$. In each shell $[3^k, 3^{k+1})$, each $d \in U_P \cap [1, W]$ contributes at most $\prod_{p \in P \setminus \{3\}}(1 + \lfloor\log_p 3^{k+1}\rfloor) = O_P(k^{|P|-1})$ insertions, so the total number of insertions in $[3^k, 3^{k+1})$ is $I_k = O_{P,W}(k^{|P|-1})$. Between consecutive insertions $[a, b) \subset [3^k, 3^{k+1})$, the shifted rational prefix $Y_n = 2^n \Pi_{P,W}^{(n)}(1/2)$ follows an exact doubling orbit $Y_n = 2^{n-a} Y_a$ modulo $q = q_{P,W,a}$, with $q$ supported on the fixed finite prime set $P_W$, polynomially bounded ($q \le D_{P,W} (3^{k+1})^{|P|}$), and growing ($q \ge 3^k$). Discard all subintervals of length $< 3^k / k^{|P|}$ (total discarded length $I_k \cdot 3^k / k^{|P|} = O_{P,W}(3^k / k) = o(3^k)$) and trim the last $\lceil 2\log_2 k \rceil$ positions of each remaining subinterval (leaving pointwise tail error $\le 2^{-\lceil 2\log_2 k \rceil} = O(k^{-2}) = o(1)$). Also discard the first $v_2(q)=O_{P,W}(k)$ positions of each retained interval. Doubling there removes its full even factor and leaves the factor $3^k$ in the denominator. For an arbitrary terminal cutoff apply the same length test to the final truncated interval; one extra short piece costs $o(3^k)$. On every remaining block of length $L \ge 3^k / (2 k^{|P|})$, the repository's smooth-orbit theorem ([Paper IV, Theorem 2.1](../../papers/04-arithmetic-certificates/paper.tex); [`SmoothOrbit.lean`](../../NormalityChecker/SmoothOrbit.lean)) — or, for $P = \{3\}$, direct splitting modulo the fixed period $\tau = \operatorname{ord}_{D_{P,W,\mathrm{odd}}}(2)$ followed by Korobov's prime-power estimate modulo $3^k$ — gives uniform cancellation of every fixed nonzero character $e(h Y_n)$. Summing across shells and applying the endpoint-coverage argument gives $D_\infty(\Pi_{P,W}(1/2)) = 0$. $\square$

### Proposition 2.2 (Pure mixed differences retain denominator rate $1$)
For every finite set of primes $P$, let $Y_N(P) := 2^N \sum_{d \in U_P,\, d \le N} d^{-1} 2^{-d}$ be the binary-shifted truncation of $g_{P,1}(1/2)$, and let $q_N(P) = \operatorname{den}(Y_N(P))$. Then
```math
\lim_{N\to\infty} \frac{\log q_N(P)}{N} = 1,
```
and the same limit $1$ holds for $Y_N(P) - 2^{N-1}$ (after removing the initial $d = 1$ term $1/2$).

**Proof.** For any prime $p \notin P$ with $p > \sqrt{N}$, multiplying $Y_N(P)$ by $p$ retains only indices $d = p\ell \le N$ with $\gcd(p\ell, \prod P) = 1$, equivalently $\ell \in U_P$ and $\ell \le N/p$. By Fermat's theorem, $p Y_N(P) \equiv 2^N \sum_{\ell \in U_P,\, \ell \le N/p} \ell^{-1} 2^{-\ell} \pmod p$. For every $v \ge 1$, the short rational sum on $N/(v+1) < p \le N/v$ is strictly positive ($\ge 1/2$, because $\ell = 1 \in U_P$ is always present!). Removing the single term $d = 1$ from $g_{P,1}(1/2)$ does **not** remove $d = p \cdot 1$ for $p > \max(P)$, so the Frobenius residue on $N/2 < p \le N$ remains $2^{N-1} \not\equiv 0 \pmod p$. For each fixed band $v$, the nonzero rational sum has only finitely many numerator prime divisors. For any fixed $V$ the first $V$ bands therefore survive for all large $N$. The prime number theorem gives their joint lower rate $1-1/(V+1)$; the lcm through $N$ gives the upper rate one. Let $V$ tend to infinity. Equivalently, by the prime-band rate formula ([`notes/strided-logarithm.md`](../strided-logarithm.md)), $\lim (\log q_N(P))/N = \sum_{v \ge 1} (\frac{1}{v} - \frac{1}{v+1}) = 1$. $\square$

**Width and precision.** The common rough denominator satisfies $\log D_{P,W}=\psi(W)-\sum_{p\in P}\lfloor\log_p W\rfloor\log p=W+o_P(W)$ for fixed $P$, by the prime number theorem. This is an estimate for a common multiple. Its growth alone gives no lower bound of exponential size on a reduced denominator, multiplicative order or first equidistributed block. At shift $j$, multiplication by $m$ inflates the raw approximation error to at most $m2^{j-W}/(W+1)$. For any target tolerance, this gives a certified range of shifts. A conclusion for ln 2 would need cancellation on a range lying inside that certified range as $W$ grows. The finite computations list the actual orders for widths through 120. The [multiplier-height theorem](multiplier-height.md) addresses a different obstruction, even when a multiplier is chosen separately at each position.

## 3. Precise solenoid representation and quantitative costs

For a finite set of distinct primes $P = \{p_1, \dots, p_r\}$ and $S = \langle P \rangle$, let $\mathbb{Z}[1/P] = \{a/m : a \in \mathbb{Z},\, m \in S\}$ and let $\mathbb{A}_P = \mathbb{R} \times \prod_{p\in P} \mathbb{Q}_p$.

### Proposition 3.1 (Canonical three-way realization of the $P$-adic solenoid)
The **$P$-adic solenoid** $\Sigma_P$ admits canonical topological-group isomorphisms
```math
\Sigma_P := \widehat{\mathbb{Z}[1/P]}
\;\cong\; \varprojlim_{m \in S} (\mathbb{T}, \times m'/m)
\;\cong\; \frac{\mathbb{R} \times \prod_{p\in P} \mathbb{Q}_p}{\Delta(\mathbb{Z}[1/P])}
\;\cong\; \frac{\mathbb{R} \times \prod_{p\in P} \mathbb{Z}_p}{\Delta(\mathbb{Z})},
```
where $\Delta(r) = (r, r, \dots, r)$ is the diagonal embedding. Under these identifications:
1. **Invertible higher-rank action.** For every $q \in P$, diagonal multiplication $\widehat{T}_q([(x_\infty, (x_p))]) = [(q x_\infty, (q x_p))]$ is a continuous group automorphism of $\Sigma_P$, turning the non-invertible $\mathbb{Z}_{\ge 0}^r$-action on $\mathbb{T}$ into an invertible $\mathbb{Z}^r$-action. Its inverse on a representative $(x_\infty, (x_p)) \in \mathbb{R} \times \prod_{p\in P}\mathbb{Z}_p$ is $[( (x_\infty - a_0)/q, ((x_p - a_0)/q)_{p\in P})]$, where $a_0 \in \{0, \dots, q-1\}$ satisfies $x_q \equiv a_0 \pmod q$ (for $p \ne q$, $q \in \mathbb{Z}_p^\times$ preserves $\mathbb{Z}_p$).
2. **Level-$m$ projections.** For each $m = \prod_{p\in P} p^{e_p} \in S$, the canonical coordinate projection $\pi_m : \Sigma_P \to \mathbb{T}$ is
   $$
   \pi_m\bigl([(x_\infty, (x_p))]\bigr) = \frac{x_\infty - (x \bmod m)}{m} \pmod 1,
   $$
   where $x \bmod m \in \{0, \dots, m-1\}$ is the Chinese remainder lift of $(x_p \bmod p^{e_p})_{p\in P}$. In particular, $\pi_1([(x_\infty, (x_p))]) = x_\infty \bmod 1$ intertwines $\widehat{T}_q$ with $T_q(x) = qx \bmod 1$, and $(m'/m)\pi_{m'} = \pi_m$ whenever $m \mid m'$.
3. **Pontryagin characters.** Each $r \in \mathbb{Z}[1/P]$ defines a continuous character $\chi_r \in \widehat{\Sigma_P}$ by
   ```math
   \chi_r\bigl([(x_\infty, (x_p))]\bigr) = e\!\left(r x_\infty - \sum_{p\in P} \{r x_p\}_p\right),
   \qquad e(u) := \exp(2\pi i u),
   ```
   where $\{u\}_p \in \mathbb{Z}[1/p] \cap [0, 1)$ is the unique $p$-adic principal part with $u - \{u\}_p \in \mathbb{Z}_p$. Well-definedness on $\Delta(\mathbb{Z}[1/P])$ is the partial-fraction identity $rs - \sum_{p\in P}\{rs\}_p \in \mathbb{Z}$ for all $r, s \in \mathbb{Z}[1/P]$. Moreover $\chi_r \circ \widehat{T}_q = \chi_{qr}$, and $\chi_{h/m}(z) = e(h\,\pi_m(z))$ for $h \in \mathbb{Z}$, $m \in S$.
4. **Local–global prefix embedding (link to Phase 14F).** For any rational prefix $Y_n \in \mathbb{Q}$ and any finite prime set $S$, write $Y_n = P_S(n) + R_S(n)$ where $P_S(n) = \sum_{p\in S} \{Y_n\}_p \in \mathbb{Z}[1/S]$ is the $S$-primary component and $R_S(n)$ has denominator coprime to $S$ (the exact split of [`notes/phase14/primary-components.md`](../phase14/primary-components.md)). Subtracting $\Delta(P_S(n)) \in \Delta(\mathbb{Z}[1/S])$ gives the exact solenoid identity
   ```math
   \bigl[(Y_n, (0)_{p\in S})\bigr] = \bigl[(R_S(n), (-P_S(n))_{p\in S})\bigr] \quad \text{in } \Sigma_S,
   ```
   verified directly for the two-stride $\ln 2$ prefix $Y_n$ with $S = \{5, 7\}$ across $30 \le n \le 60$ in [`scripts/phase15_projection.py`](../../scripts/phase15_projection.py).

In the compact model use the representative with real coordinate $r\in[0,1)$. A local residue $c\bmod m$ and real interval $I$ correspond to $\pi_m\in(I-c)/m\bmod1$, of Haar measure $|I|/m$. A circle discrepancy estimate for the level must resolve that scale to control its relative error. On the archimedean leaf $\pi_m([(y,0)])=y/m\bmod1$. Equality of finitely many primary residues leaves this real coordinate free. The Phase 14 perturbations preserve specified local primary data, while the phase at level one can change. Conversely, two points equal *in the solenoid* necessarily agree at level one. [Primary countermodels](../phase14/primary-components.md)

For a binary invariant measure $\mu$, the first digit and the first $k-1$ change indicators determine the first $k$ digits. By entropy subadditivity and stationarity this gives $h_\mu(T_2)\le H_2(\mu([1/4,3/4)))\log2$. Zero transition probability forces the binary process to be constant almost surely, hence the circle measure is $\delta_0$ (both constant words represent zero on the circle). In an empirical limit the transition interval is a continuity set: a doubling-invariant probability has zero mass at the strictly preperiodic endpoints. No extra invariance under three follows from the binary average.

## 4. Induced return equivalences, unfinished runs, and aggregate long-run estimates

Let $E = [1/4, 3/4) \subset \mathbb{T}$ be the binary transition set. For any non-dyadic $y \in \mathbb{T}$ (in particular every irrational), define the first-return time $r_E(y) := \inf\{k \ge 1 : T_2^k(y) \in E\}$ and the induced map $T_E(y) := T_2^{r_E(y)}(y)$ on $E$.

### Proposition 4.1 (Exact geometry of the induced return map and cosine-spike link)
For every non-dyadic $y \in E = [1/4, 3/4)$:
1. **Exact return-time partition.** Writing $E_0 = [1/4, 1/2)$ (`01...`) and $E_1 = [1/2, 3/4)$ (`10...`), for every $k \ge 1$:
   $$
   r_E(y) = k \iff 2^{-(k+2)} < \left|y - \frac{1}{2}\right| < 2^{-(k+1)},
   \qquad\text{so}\qquad
   r_E(y) = \left\lfloor -\log_2\left|y - \frac{1}{2}\right|\right\rfloor - 1.
   $$
   On each cylinder, $T_E$ maps $E_0 \cap \{r_E = k\}$ affinely onto $E_1$ with slope $2^k$, and $E_1 \cap \{r_E = k\}$ affinely onto $E_0$ with slope $2^k$. With normalized Lebesgue measure $\mu_E = 2\,\mathrm{Leb}|_E$, $r_E$ is $\mathrm{Geom}(1/2)$ ($\mu_E(r_E = k) = 2^{-k}$) with Kac integral $\int_E r_E\,d\mu_E = 2 = 1/\mathrm{Leb}(E)$.
2. **Two-sided cosine-spike equivalence.** For $v(y) := -\log|\cos(\pi y)|$ ([`notes/classical-discrepancy.md`](../classical-discrepancy.md)),
   ```math
   \bigl(r_E(y) + 1\bigr)\log 2 - \log\pi \;<\; v(y) \;<\; \bigl(r_E(y) + 1\bigr)\log 2.
   ```

**Proof.** On $E_0$, $y = 0.0\,1^k 0\dots$ satisfies $1/2 - y \in (2^{-(k+2)}, 2^{-(k+1)})$ and returns to $E_1$ at step $k$ via $2^k y - (2^{k-1}-1)$; $E_1$ is symmetric under $y \mapsto 1 - y$. On $E$, $|\cos(\pi y)| = \sin(\pi |y - 1/2|)$ obeys $2|y - 1/2| \le |\cos(\pi y)| \le \pi|y - 1/2|$. Substituting $2^{-(r_E+2)} < |y - 1/2| < 2^{-(r_E+1)}$ and taking $-\log$ gives both bounds. $\square$

Now fix an irrational $x \in \mathbb{R} \setminus \mathbb{Q}$, and let $0 \le t_1 < t_2 < \dots$ be the transition times ($T_2^{t_m}(x) \in E$). Put $r_0 := t_1$, completed return times $r_m := t_{m+1} - t_m = r_E(T_2^{t_m}(x)) \ge 1$ ($m \ge 1$), and at integer cutoff $N \ge 1$ let $K(N) := \#\{0 \le n < N : T_2^n(x) \in E\}$, $\tau_N(x) := K(N)/N$, and $t(x) := \liminf_{N\to\infty}\tau_N(x)$. When $K(N) \ge 1$, define the **unfinished run length**
$$
\widetilde{u}_N := N - t_{K(N)} \in [1, r_{K(N)}],
\qquad
\text{so}\qquad
N = r_0 + \sum_{m=1}^{K(N)-1} r_m + \widetilde{u}_N.
$$
For any integer threshold $L \ge 1$, define the **long-run excess** (with and without the unfinished run) and **long-run tail mass**:
```math
\mathcal{E}_L(N) := \sum_{m=1}^{K(N)-1}(r_m - L)_+ + (\widetilde{u}_N - L)_+,
\qquad
\mathcal{E}_L^{\mathrm{comp}}(N) := \sum_{m=1}^{K(N)-1}(r_m - L)_+,
```
```math
\mathcal{M}_L(N) := \sum_{\substack{m=1 \\ r_m > L}}^{K(N)-1} r_m + \widetilde{u}_N\,\mathbf{1}_{\widetilde{u}_N > L}.
```

### Theorem 4.2 (Induced-return equivalences and dyadic-cutoff transfer)
Let $x \in \mathbb{R} \setminus \mathbb{Q}$. The following six conditions are equivalent:
1. $D_\infty(x) < 1$.
2. $t(x) = \liminf_{N\to\infty} \tau_N(x) > 0$.
3. $\overline{R}(x) := \limsup_{M\to\infty} \frac{1}{M}\sum_{m=1}^M r_m < \infty$. In fact, for **every** irrational $x$,
   ```math
   t(x) = \frac{1}{\overline{R}(x)},
   \qquad
   \limsup_{N\to\infty} \tau_N(x) = \frac{1}{\underline{R}(x)},
   \qquad \underline{R}(x) := \liminf_{M\to\infty}\frac{1}{M}\sum_{m=1}^M r_m.
   ```
4. There exists $L \ge 1$ with $\limsup_{N\to\infty} \mathcal{E}_L(N)/N < 1$. Quantitatively, $\limsup_{N\to\infty} \mathcal{E}_L(N)/N \le \alpha < 1$ implies $t(x) \ge (1 - \alpha)/L$, and conversely $\limsup_{N\to\infty} \mathcal{E}_L(N)/N \le 1 - t(x)$ for every $L \ge 1$.
5. There exists $L \ge 1$ with $\limsup_{N\to\infty} \mathcal{M}_L(N)/N < 1$. Quantitatively, $\limsup_{N\to\infty}\mathcal{M}_L(N)/N \le \beta < 1$ implies $t(x) \ge (1 - \beta)/L$, and conversely $\limsup_{N\to\infty}\mathcal{M}_L(N)/N \le 1 - t(x) + \frac{1}{L+1} < 1$ for every $L > 1/t(x) - 1$ (the periodic example with constant runs of integer length $R$ illustrates the threshold and gives $\mathcal{M}_{R-1}(N)/N \to 1$ and $\mathcal{M}_R(N)/N = 0$).
6. (**Dyadic cutoffs including the unfinished run.**) There exists $L \ge 1$ with $\limsup_{m\to\infty} \mathcal{E}_L(2^m)/2^m < 1$. Quantitatively,
   ```math
   \limsup_{m\to\infty} \frac{\mathcal{E}_L(2^m)}{2^m} \le \alpha < 1
   \quad\Longrightarrow\quad
   t(x) \ge \frac{1 - \alpha}{(1 + \alpha)\, L} > 0,
   ```
   This is a sufficient lower bound.

**Proof.**
*(1) $\Leftrightarrow$ (2)* is the repository's sharp binary discrepancy theorem ([`notes/transition-discrepancy.md`](../transition-discrepancy.md)).

*(2) $\Leftrightarrow$ (3)*: Since $x$ is irrational, $K(N) \to \infty$. At any $N$ with $K = K(N) \ge 1$, $t_K + 1 \le N \le t_{K+1}$, so
$$
\frac{r_0 + 1 + \sum_{m=1}^{K-1} r_m}{K} \le \frac{N}{K(N)} \le \frac{r_0 + \sum_{m=1}^{K} r_m}{K}.
$$
Taking $\limsup$ and $\liminf$ over $N$, and evaluating along the extremal subsequences $N_M = t_{M+1}$ (where $K(N_M) = M$ and $\widetilde{u}_{N_M} = r_M$) and $N'_M = t_M + 1$ (where $K(N'_M) = M$ and $\widetilde{u}_{N'_M} = 1$), yields both exact reciprocal identities.

*(2) $\Leftrightarrow$ (4)*: Using $r = \min(r, L) + (r - L)_+ \le L + (r - L)_+$ on each completed run and on $\widetilde{u}_N$,
$$
N - r_0 = \sum_{m=1}^{K(N)-1} r_m + \widetilde{u}_N \le L \cdot K(N) + \mathcal{E}_L(N),
$$
giving $\tau_N(x) \ge (1 - \mathcal{E}_L(N)/N - r_0/N)/L$. Conversely, $\min(r, L) \ge 1$ for every $r \ge 1$, so $\mathcal{E}_L(N) \le N - r_0 - K(N) \implies \mathcal{E}_L(N)/N \le 1 - \tau_N(x)$.

*(2) $\Leftrightarrow$ (5)*: Since $\mathcal{E}_L(N) \le \mathcal{M}_L(N)$, $\limsup \mathcal{M}_L(N)/N \le \beta < 1$ implies $t(x) \ge (1-\beta)/L$ by (4). Conversely, every run $> L$ has length $\ge L+1$, so at most $N/(L+1)$ runs in $[0, N)$ exceed $L$. The remaining at least $K(N) - N/(L+1)$ runs each have length $\ge 1$ and lie outside $\mathcal{M}_L(N)$, giving $\mathcal{M}_L(N) \le N - r_0 - (K(N) - N/(L+1))$. Dividing by $N$ gives $\limsup \mathcal{M}_L(N)/N \le 1 - t(x) + 1/(L+1)$.

*(2) $\Leftrightarrow$ (6)*: Clearly (4) $\Rightarrow$ (6). For the converse, note the **two monotonicity laws** of $\mathcal{E}_L(n)$ (both of which depend crucially on including the unfinished run $\widetilde{u}_n$!): advancing $n \to n+1$ leaves $\mathcal{E}_L$ unchanged if $n$ is a transition (since $\widetilde{u}_n$ moves into the completed sum and $\widetilde{u}_{n+1} = 1$ adds $(1-L)_+ = 0$) and increases $\mathcal{E}_L$ by $0$ or $1$ otherwise. Thus $\mathcal{E}_L(n+1) - \mathcal{E}_L(n) \in \{0, 1\}$, which means **both** $n \mapsto \mathcal{E}_L(n)$ and $n \mapsto n - \mathcal{E}_L(n)$ are nondecreasing! For any $N = \theta \cdot 2^m$ with $\theta \in [1, 2)$,
$$
N - \mathcal{E}_L(N) \ge 2^m - \mathcal{E}_L(2^m)
\qquad\text{and}\qquad
N - \mathcal{E}_L(N) \ge N - \mathcal{E}_L(2^{m+1}).
$$
Dividing by $N = \theta \cdot 2^m$ and letting $m \to \infty$ gives
$$
\liminf_{N\to\infty} \frac{N - \mathcal{E}_L(N)}{N}
\ge \inf_{\theta \in [1,2)} \max\!\left(\frac{1 - \alpha}{\theta},\; 1 - \frac{2\alpha}{\theta}\right)
= \frac{1 - \alpha}{1 + \alpha},
$$
attained at $\theta = 1 + \alpha \in [1, 2)$. Dividing by $L$ gives $t(x) \ge \frac{1 - \alpha}{(1+\alpha)L}$. This proves the stated lower bound.

### Theorem 4.3 (Why the unfinished run cannot be dropped on dyadic cutoffs)
Use zero-based fractional digit indices. Take the alternating binary word and overwrite its digits with zero on the intervals $[\lfloor Q_j/(j+1)\rfloor,Q_j+2)$ where $Q_j=2^{4j+(\max(j-4,0))^2}$. These blocks are eventually disjoint, and the total length of earlier blocks is $o(Q_j/(j+1))$. Arbitrarily long alternating and constant stretches imply irrationality. Fix an integer $L\ge1$. At cutoff $Q_j$, the current zero run is unfinished and has age $Q_j(1-o(1))$. Hence its full excess fraction tends to one and the transition frequency tends to zero. At $2Q_j$ that run is completed, contributing $(1/2-o(1))$ to the completed excess divided by the cutoff. Between $2Q_j$ and $Q_{j+1}$ the total completed excess is at most $(1+o(1))Q_j$: outside the overwritten intervals all runs have length one, with at most a bounded endpoint adjustment per block. There is no dyadic cutoff strictly between $Q_j$ and $2Q_j$. Consequently the upper limit of the *completed* excess fraction on dyadic cutoffs is exactly $1/2$, while the full excess has upper limit one. This proves the need for the unfinished term.

**Aggregate moments.** Write $S_p(N)=\sum_{m<K(N)}r_m^p+\widetilde u_N^p$, where the sum starts at $m=1$. If $S_p(N)\le C N^\gamma$ for all large $N$, with $1<\gamma<p$, put $\beta=(\gamma-1)/(p-1)$. Then
$$
1-D_N(x)\ \ge\ \left(\frac{\beta}{C^{1/(p-1)}\log2}-o(1)\right)\frac{\log N}{N^\beta}.
$$
Here the moment is an arithmetic hypothesis. For the proof the completed lengths sum to $M=N-o(N)$ since the unfinished length is at most $C^{1/p}N^{\gamma/p}$. Set $S_0=C N^\gamma$, $t=(p-1)(S_0/M)^{1/(p-1)}/p$ and $c_p=(p-1)^{p-1}/p^p$. For $t\ge L$, one has $\min(r,L)\ge L(r/t-c_p(r/t)^p)$: for $r/t\ge1$ maximize $(u-1)/u^p$ and for $r/t<1$ use $L\le t$. Summing gives $\sum\min(r_m,L)\ge L(M^p/S_0)^{1/(p-1)}$. Choose $L=\lfloor\beta\log_2 N-2\log_2\log N\rfloor$ and $s=L(M^p/S_0)^{1/(p-1)}/N$. Then $L\le t$ and $2^{-L-1}>2s$ eventually. The last $\min(r_m,L)$ positions through each completed run's ending transition have circle distance at least $2^{-L-1}$, by the doubling Lipschitz bound. They occupy disjoint positions in $[0,N)$, so the frequency in $[2s,1-2s)$ is at least $s$. The repository's finite interior-frequency lemma gives $1-D_N\ge s$, as asserted. This improves the rate obtained from counting transitions alone. An optimal leading constant for a fixed infinite word is unproved. [Interior-frequency lemma](../../NormalityChecker/LogarithmTransitionBounds.lean)

## 5. Primary-source review and generic vs. specific $\ln 2$

Furstenberg's closed-set theorem makes the joint $\times2,\times3$ orbit of every irrational dense; a sparse binary word already shows that this does not force binary escape. Rudolph's theorem for coprime generators, and Johnson's extension to multiplicatively independent generators, give Lebesgue measure for jointly invariant, ergodic measures under a positive-entropy hypothesis. A binary empirical measure need satisfy only doubling invariance. Even when a second invariant measure is available, an almost-everywhere conclusion such as Host's requires a separate argument for one prescribed number. Lagarias relates the perturbed radix recurrence to the true orbit and compares Bailey–Crandall's Hypothesis A to Furstenberg's measure question. Its alternative uses a **finite attractor**, which need not be an eventually periodic sequence of perturbed points. For ln 2 the perturbation is $1/n$ and the required orbit estimate is open. [Furstenberg](https://doi.org/10.1007/BF01692494) · [Rudolph](https://doi.org/10.1017/S0143385700005629) · [Host](https://doi.org/10.1007/BF02761660) · [Lagarias](https://arxiv.org/abs/math/0101055)

For the normalized Lebesgue measure on the transition region, the return law is geometric with generating function $z/(2-z)$ and mean two. For a specified orbit the successive gaps need not be independent. In a formal power series the transition count has generating series $\sum_j z^{t_j}/(1-z)$ for counts through index $N$ inclusive. Replacing the exponents by a renewal process would require an additional law for the gap sequence. The experiment prints certified transition counts, full and completed excess and run moments for the logarithm and explicit comparison words. They supply finite tests for the missing bounded-mean-return estimate. [Code](../../scripts/phase15_projection.py)
