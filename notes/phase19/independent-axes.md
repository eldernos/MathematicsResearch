# A polynomial-normal algebra with distinct retained primes

Given an integer $b\ge2$ and any finite list of distinct off-radix primes $p_1,\ldots,p_m$, one can construct **positive** series $X_i$ on one schedule such that the coefficient of series $i$ at step $k$ has reduced denominator exactly $p_i^{E_k}$, and **every nonconstant rational polynomial** $P(X_1,\ldots,X_m)$ is normal in base $b$ and Liouville. The $X_i$ are algebraically independent. The proof protects a prime belonging to a variable that occurs in $P$ by controlling the other numerators modulo that prime. There is no common retained prime shared by the coefficient denominators.

The construction works on every strictly increasing sequence of positive integers $n_k$ with $n_{k+1}/n_k\to\infty$. One computable choice, much denser than factorial, is $n_k=\prod_{h=1}^k(2+\lceil\log_2(h+1)\rceil)$, with $\log n_k=O(k\log\log(k+2))$. The alternative rapid-variation theorem for a *single* valuation-weighted series even allows the consecutive ratios to tend to one. [Single-series theorem](nonlinear.md#2-universal-polynomial-normality-with-consecutive-ratios-tending-to-one)

## Programming the other axes locally

For each $i$, choose a tuple $(\theta_{ij})_{j\ne i}$ in $\mathbb Z_{p_i}^{m-1}$ algebraically independent over $\mathbb Q$. For one generator this tuple is empty. These tuples can be computed: enumerate nonzero integer polynomials in $m-1$ variables. Given a finite product of residue balls and the next polynomial, search their integer representatives for a point where its value is nonzero. Each ball contains infinitely many integers and a nonzero polynomial cannot vanish on their Cartesian product. Refine each ball about this point to depth greater than the valuation of the value and greater than the previous depth. Integrality of the coefficients preserves the nonzero residue throughout this product. Iteration determines the desired computable tuple.

Use $E_k=Ck+\lfloor\log_2 n_k\rfloor$ with a positive integer $C$ chosen so $p_j^{Ck}\ge p_j\prod_{i\ne j}p_i^k$ for every $j,k\ge1$. For $U_{j,0}=0$ choose $A_{j,k}$ by
$$
 A_{j,k}\equiv1\bmod p_j,\qquad
 A_{j,k}\equiv p_j^{E_k} b^{n_k}(\theta_{ij}-U_{j,k-1})\bmod p_i^k\quad(i\ne j).
$$
Take the least positive representative modulo $p_j\prod_{i\ne j}p_i^k$. The congruences are defined since earlier $U_{j,k-1}$ have denominators supported on $p_j$ and divisors of $b$. Put
$$
 V_{j,k}=(A_{j,k}/p_j^{E_k})b^{-n_k},\qquad
 U_{j,k}=U_{j,k-1}+V_{j,k},\qquad X_j=\sum_{k\ge1}V_{j,k}.
$$
The weights are in $(0,1]$ by choice of $C$. At $p_i$, the own prefix $U_{i,k}$ has valuation $-E_k$ by its unique deepest term. For $j\ne i$ one has $U_{j,k}\equiv\theta_{ij}\bmod p_i^k$, and hence $v_{p_i}(V_{j,k})\ge k-1$ for $k\ge2$. Also $E_k-E_{k-1}\to\infty$ and $E_k=O(\log n_k)$, since $n_k$ grows at least geometrically eventually.

## The surviving term of a general polynomial

Clear fixed rational coefficients and take $P$ integral of total degree $r\ge1$. Choose a variable $i$ occurring with degree $q\ge1$, and write $f$ for the polynomial coefficient of $X_i^q$ in the other variables. Here $U_{-i,k}$ denotes the tuple of all prefixes except coordinate $i$, and $\theta_{i,-i}$ their prescribed local limits. Since $f(\theta_{i,-i})\ne0$, $v_{p_i}(f(U_{-i,k-1}))=g$ is a fixed finite integer for all large $k$.

Consider the unshifted convolution prefix of $P(X)$ at $n_k\le n<n_{k+1}$. Exclude windows $[j n_k,j n_k+r n_{k-1}]$ for $1\le j\le r$. For large $k$, all tuples of earlier terms already fit at $n_k$. On the rest of the shell the prefix is precisely the sum through degree $\ell=\min(r,\lfloor n/n_k\rfloor)$ in the auxiliary variable $z$ of $P(U_{k-1}+zV_k)$, evaluated at $z=1$. Indeed a tuple with $h$ occurrences of the newest index costs an exponent between $h n_k$ and $h n_k+r n_{k-1}$. The discarded windows have upper density zero, including when the observation cutoff ends inside one: their cumulative length through shell $k$ is $O_r(\sum_{a\le k} (n_{a-1}+1))=o(n_k)$, taking $n_0=0$.

Let $t=\min(q,\ell)$ and $\Delta_k=E_k-E_{k-1}$. In this truncated polynomial the term using degree $q$ in variable $i$, exactly $t$ new occurrences of $i$, and **no** new occurrence of another axis is
$$
 \binom qt\, U_{i,k-1}^{\,q-t}V_{i,k}^{\,t}\, f(U_{-i,k-1}).
$$
It has pole depth $qE_{k-1}+t\Delta_k-g-v_{p_i}\binom qt$. A lower degree in $i$ loses at least $E_{k-1}$ from the nominal depth $qE_{k-1}+t\Delta_k$; it cannot have more than $t$ new occurrences of $i$. A term of the same degree with fewer new occurrences of $i$ loses at least $\Delta_k$. At the same degree and same number $t$, any remaining term must include a new occurrence on a different axis and loses at least $k-1$. Integer coefficients and integral other-axis prefixes cannot reverse these losses. The grouped displayed term therefore has strictly largest pole for all sufficiently large $k$, simultaneously for the finitely many possible $t$. Multiplication by $b^n$ preserves it. Thus the stated pole depth is exact outside the exceptional windows.

Every shifted denominator is supported on the fixed set of the $p_i$ and is bounded by $\prod_i p_i^{rE_k}=n_k^{O_P(1)}$ in this shell. There are $O_P((\log(2N))^r)$ tuple insertions through $N$, and polynomially bounded coefficient mass per exponent from the bounded input weights. The growing pole off a density-zero set now gives all-prefix normality by the [Phase 18 arithmetic criterion](../phase18/principal.md#a-fixed-support-criterion-for-all-prefixes). Rational dilation removes the coefficient-clearing factor. A nonzero polynomial relation would give the constant zero, contradicting normality. In particular the construction works simultaneously for all polynomials without selecting the real inputs anew for each $P$.

For Liouville approximation, $P(U_{1,k},\ldots,U_{m,k})$ has reduced denominator at most $(b^{n_k}\prod_i p_i^{E_k})^r$ times a fixed coefficient denominator, and error $O_P(b^{-n_{k+1}})$ by boundedness of derivatives on a compact box containing all prefixes and limits. The limit is irrational by normality, so these errors are nonzero and the rational denominators tend to infinity. For each fixed $h$ one has $n_{k+1}>h(rn_k+O_P(\log n_k))+O_P(1)$ eventually, so the strictly positive absolute error is smaller than the reduced denominator to power $-h$. This proves the Liouville assertion. The construction uses deliberate cross-prime congruences. Arbitrary independent-prime products, in particular the original mixed Stoneham product, do not come with that hypothesis.

The local independence of the prescribed residues is an input to the leading-coefficient test at each chosen prime. Real algebraic independence of the resulting numbers is a consequence of the normality theorem. Its large-index threshold can depend on the polynomial. [Independent proof audit](reviews/independent-axes.md) · [Exact CRT checks](../../scripts/phase19_independent_axes.py)
