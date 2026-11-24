# Persistent cancellation at every positive order

Let $b\ge 2$ be an integer, $A$ a finite set of primes, $s\ge 1$ an integer and $J=\{p\in A:p\nmid b\}$. Let $M(A)$ consist of the positive integers with prime divisors in $A$, including 1. Consider

$$
X_s=\sum_{m\in M(A)}\frac{b^{-m}}{m^s},
\qquad R_{s,n}=\sum_{m\in M(A),\ m\le n}\frac{b^{n-m}}{m^s}.
$$

Write $D_N$ for the largest absolute discrepancy of the first $N$ fractional parts $\{b^n X_s\}$ over half-open subintervals of $[0,1)$. For each $p\in J$ and $1\le d\le s$, let $Z_{p,d}$ be the intersection of the checker's failed regions over every precision at order $d$. For $y\ge 1$ put $t_p(y)=y/p^{\lfloor\log_p y\rfloor}$. Let $B$ consist of the $y\ge 1$ satisfying $t_p(y)\in Z_{p,d}$ for every pair $(p,d)$.

**Theorem (Lean).** Along every positive integer cutoff,

$$
D_N-\frac{|B\cap[1,N)|}{N}\longrightarrow0.
$$

At precision $L$, test all of these pairs using the existing integer checker. Let $F_L(N)$ count their simultaneous failures before $N$. Then

$$
\lim_{L\to\infty}\limsup_{N\to\infty}\frac{F_L(N)}{N}
=\limsup_{N\to\infty} D_N.
$$

Both statements include empty support and empty $J$. For empty $J$, the real mass is $(N-1)/N$ at $N\ge1$, so $D_N\to1$. Lean indexes precision $L$ by $l=L-1$. [All-prefix theorem and finite-checker density theorem](../NormalityChecker/HigherOrderPrefix.lean) · [Denominator bounds and the all-base limit](../NormalityChecker/HigherOrderDiscrepancy.lean)

## A finite principal-unit identity

Fix $p\in J$ and put $S=A\setminus\{p\}$. Hensel's lemma applied to $X^p-X$ at the inverse radix gives $w,z\in\mathbb Z_p$ with $w^p=w$, $|w|_p=1$ and $b^{-1}=w(1+pz)$. For each digit position $n$, use the Newton polynomial

$$
P_n(X)=\sum_{j=0}^n \frac{p^j z^j}{j!}\prod_{i=0}^{j-1}(X-i).
$$

Legendre's bound $v_p(j!)\le j$ makes all its coefficients integral. At each integer $0\le m\le n$ the binomial theorem gives $P_n(m)=(1+pz)^m$. Write $c_{n,h}$ for the coefficient of $X^h$. Dividing by $m^s$ makes all terms of degree at least $s$ integral. The same polynomial works for every insertion through the given position. [Interpolation, factorization and exact prefix identity](../NormalityChecker/HigherOrderPrincipal.lean)

For $1\le t<p$ and positive $d$ put

$$
U_d(t)=\sum_{i\ge0}p^{id}
 \sum_{r\in M(S),\ r\le tp^i}\frac{w^r}{r^d}.
$$

Each cofactor is a $p$-adic unit. The row norms are bounded by $p^{-id}$, and the part from $i\ge k+1$ is a multiple of $p^{(k+1)d}$ in $\mathbb Z_p$. Fix $n\ge1$, $y\in[n,n+1)$, $k=\lfloor\log_p n\rfloor$ and $t=y/p^k$. Splitting $m=p^{k-i}r$ in the prefix gives exactly the first $k+1$ rows of the normalized frozen moment. Here $w^m=w^r$ and $\lfloor tp^i\rfloor=\lfloor n/p^{k-i}\rfloor$. The omitted rows remain integral after scaling by $p^{-kd}$. Consequently

$$
b^{-n}R_{s,n}\equiv
  \sum_{h=0}^{s-1} c_{n,h}\,p^{-k(s-h)}U_{s-h}(t)
  \pmod{\mathbb Z_p}.
$$

Reduction of $U_d(t)$ modulo $p^L$ gives exactly the checker's order-$d$ residue at $\lfloor t p^{L-1}\rfloor$. Indeed $(1+pz)^{p^{L-1}}\equiv1\pmod{p^L}$, so $w$ reduces to the checker's canonical inverse-radix lift. This works on either side of an insertion, including the insertion itself with its half-open cell convention. Hence $U_d(t)=0$ exactly on $Z_{p,d}$. Simultaneous zeros clear $p$ from the reduced denominator of $R_{s,n}$. [Checker reduction and zero-set equivalence](../NormalityChecker/HigherOrderCells.lean) · [Prime clearing](../NormalityChecker/HigherOrderPrincipal.lean)

## Detecting the largest nonzero order

The coefficients $c_{n,h}$ vary with $n$. For odd $p$, finite differences give a uniform lower bound on their norms for $0\le h\le s$ and all sufficiently large $n$. Let $u=1+pz$ and $v=v_p(b^{p-1}-1)$. Set $a=vs+1$ and $T=(p-1)p^a$. Once $n\ge sT$, take the $h$-th difference of $P_n$ on $0,T,\ldots,hT$. The difference of the exponential values is $(u^T-1)^h$. Lower polynomial degrees cancel, degree $h$ contributes $h!T^hc_{n,h}$, and all higher degrees contribute a multiple of $T^{h+1}$ in $\mathbb Z_p$.

Since $w^{p-1}=1$, the lifting-the-exponent identity gives $v_p(u^T-1)=v+a$. The main side has valuation $h(v+a)<(h+1)a$, so the error cannot cancel it. In particular $|c_{n,h}|_p\ge p^{-s(v+a)}$ uniformly. This argument also covers $h=0$. [Finite difference identity and coefficient bound](../NormalityChecker/HigherOrderDominance.lean)

Let $d$ be the largest order with $U_d(t)\ne0$, and assume $|U_d(t)|_p\ge p^{-L}$. Write $C=s(v+a)$. In the local identity the order-$d$ term has norm at least $p^{kd-C-L}$. The smaller orders and the integral remainder have norm at most $p^{k(d-1)}$. For $k>C+L$ the order-$d$ term therefore determines the norm of the whole sum. Since $b$ is a $p$-adic unit and the norm of a rational is at most its reduced denominator, that denominator is at least $p^{k-C-L}$. For $p=2$ the first mesh already certifies normality at every order. [Dominant-order denominator theorem](../NormalityChecker/HigherOrderDominance.lean) · [Prime-two theorem](../NormalityChecker/MaximalSupport.lean)

## Passing from real phases to every cutoff

Let $c$ be the product of the off-radix primes. On clean blocks every shifted denominator divides a power of $c$. Positions at which the denominator is coprime to $c$ therefore give integral prefixes there. The shifted tail tends to zero, so these positions avoid a fixed interval $[\delta,1-\delta)$ for large starts. The clean-block transfer absorbs the initial, recent-insertion and incomplete blocks uniformly in the cutoff. This proves that the coprime-denominator share minus any fixed positive error is eventually a lower bound for $D_N$. Every real point of $B$ gives this coprimality at its digit position. The length of each digit interval is one.

For the upper bound fix a precision $L$. The discarded one-coordinate error sets are the finite-level failed regions minus their persistent sets. Each has length tending to zero by continuity of measure from above. For any such set $E\subset[1,p)$, the positions before $N$ with $t_p(y)\in E$ have total length at most $2N|E|$. Indeed scale $j$ has length contribution at most $p^j|E|$, and summing through the cutoff scale costs at most $pN/(p-1)$. Sum these errors over the finitely many pairs.

Mark a digit position if its entire real unit interval lies in $B$ or in the union of the error sets, allowing different points to lie in different sets. At any unmarked late position a real witness supplies a prime and largest nonzero order whose norm exceeds $p^{-L}$. The denominator then grows uniformly by the preceding estimate. One such position suffices for its whole clean block, because its reduced denominator divides the starting denominator. The short-orbit estimate bounds every interval's discrepancy on the block. Marked positions cost at most the length of $B$ plus the discarded length. Let the precision grow to obtain the asserted all-prefix limit. For the finite-checker version, each fixed mesh is constant on real unit intervals after finitely many scales. The early difference is $O_{A,L}(1/N)$ and the same discarded widths control the remaining loss. [Clean transfer](../NormalityChecker/WeightedBlocks.lean) · [Prefix bounds and both limits](../NormalityChecker/HigherOrderPrefix.lean)

## Relation to compact phases

For $y=Nu$ one has $t_p(y)=p^{\{\log_p N+\log_p u\}}$ wherever $y\ge1$. Thus the normalized length in the theorem differs from the compact phase score $Q_B$ at the log phase of $N$ by at most $1/N$. The finite-level scores are continuous by dominated convergence away from their countably many boundary preimages. Summing the one-coordinate geometric bounds gives uniform convergence for the persistent score. The maximization over the closure of the real log flow and the distinction between ordinary and logarithmic density are detailed in the joint-persistence note. The executable finite tests and the Lean limit theorems above use ordinary cutoffs. [Compact phase formula and recurrence proof](joint-persistent.md#the-compact-set-of-attainable-phases-paper-proof)
