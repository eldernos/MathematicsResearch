# Normality of unsigned expansions on every mixed finite prime support

Fix integers $b\ge2$ and $s\ge1$. Let $P$ be a finite set of primes, and let $M(P)$ be the positive integers whose prime factors belong to $P$, including 1. Define
$$
X=\sum_{m\in M(P)}\frac1{m^s b^m}.
$$
**Theorem (paper).** If some $p\in P$ does not divide $b$, then $X$ is normal in radix $b$. If every prime in $P$ divides $b$, its interval discrepancy tends to one. Thus these unsigned full-support expansions have just two asymptotic discrepancy values, zero and one. This includes every positive denominator order and arbitrary overlap between the radix factors and the support. The proof gives no uniform rate as the support grows, and the unrestricted series for $\ln2$ has infinitely many support primes.

Lean verifies the modular certificate, the passage from fails of small width to discrepancy bounds, and the all-base maximal case. It also verifies the positive-measure recurrence, tail periodicity and finite-lattice separation lemmas used below. The assembly of the null-set proof for the unsigned expansion in this note is a paper deduction. [Finite test](../NormalityChecker/LocalizedCertificate.lean) · [Discrepancy bound](../NormalityChecker/DiscrepancyChecker.lean) · [Supporting lemmas](../NormalityChecker/ThresholdDifferences.lean) · [Maximal discrepancy](../NormalityChecker/MaximalSupport.lean)

## From prime residues to a measurable function

Fix a single $p\in P$ coprime to $b$, and write $S=M(P\setminus\{p\})$. For $p=2$ the existing first-cell theorem already proves normality. For odd $p$, let $w$ be the Teichmüller lift in $\mathbb Z_p^\times$ of $b^{-1}\bmod p$. Thus $w^{p-1}=1$. For every real $t>0$, set
$$
V(t)=\sum_{i\in\mathbb Z}p^{is}
       \sum_{\substack{m\in S\\m\le p^i t}}\frac{w^m}{m^s}.
$$
The inner sums are finite. On every compact positive $t$-interval all sufficiently negative rows are empty, and rows at large positive $i$ have valuation at least $is$. The step functions therefore converge uniformly in the $p$-adic metric there. The zero set is measurable. Changing $t$ to $pt$ shifts the row index and gives $V(pt)=p^{-s}V(t)$.

On $[1,p)$ the negative rows are empty. Reduction of $V$ modulo $p^L$ is exactly the checker's failed-cell test at precision $L$. Indeed the canonical inverse lift of the base modulo $p^L$ is $w\bmod p^L$, only rows with $is<L$ can contribute, and on the integer mesh the row cutoff is $\lfloor p^i t\rfloor$. Thus the intersection of all failed regions is $Z=\{t\in[1,p):V(t)=0\}$. Their lengths decrease to $|Z|$. If $|Z|=0$, the finite upper bound on discrepancy tends to zero: on every geometric scale a failed part has width at most the total failed width, and the sum of the completed scale lengths and the current scale weight is at most $pN/(p-1)$ at every prefix cutoff $N$. The soundness theorem then proves normality. It suffices to show $|Z|=0$ separately for this prime. [Canonical lift and residue](../NormalityChecker/LocalizedCertificate.lean) · [Single-prime bound and refinement](../NormalityChecker/DiscrepancyChecker.lean) · [Limit regions](joint-persistent.md)

If $S=\{1\}$, the sum on $[1,p)$ is the unit $w/(1-p^s)$ and there are no failures. Otherwise choose one cofactor prime $r$ to retain. Denote the remaining cofactor primes by $q_1,\ldots,q_d$. We give the argument also for $d=0$.

## Removing all but one unbounded exponent

Suppose $|Z|>0$. In the coordinate $\log_p t\bmod1$ it has positive Haar measure, since $dt/t$ and $dt$ are equivalent on $[1,p)$. For a cofactor $q$ let $h_q\ge1$ be an eventual period of $q^j\bmod (p-1)$, with preperiod $L_q$. These parameters exist even when $q$ shares primes with $p-1$.

For a function $G$ satisfying $G(pt)=p^{-s}G(t)$, put
$$
(\Delta_{q,a}G)(t)=G(t)-q^{-as}G(t/q^a).
$$
The difference has the same scaling law. If the zero set of $G$ on the log circle has positive measure, the rotation by $-h_q\log_p q$ has a positive iterate whose return intersection with this zero set has positive measure. This is finite-measure Poincaré recurrence. Indeed, if every positive iterate had null intersection, all the inverse translates of the zero set would be pairwise disjoint up to null sets, contradicting finite total measure. Choose $a$ to be the corresponding positive multiple of $h_q$. On the return intersection $G(t)$ and $G(t/q^a)$ both vanish, including when these points use different scale representatives. Hence $\Delta_{q,a}G$ also has a positive-measure zero set. Repeat once for each $q_i$. The chosen exponents are finite and may depend on earlier choices. For $d=0$ use $G=V$ unchanged. [Lean finite recurrence](../NormalityChecker/ThresholdDifferences.lean)

Write $Q_I=\prod_{j\in I}q_j^{a_j}$ for subsets $I$ of the processed generators. After all differences the row function is
$$
G(t)=\sum_i p^{is}\sum_{\substack{m\in S\\m\le p^i t}}\frac{A(m)}{m^s},
\qquad
A(m)=\sum_{\substack{I\\ Q_I\mid m}}(-1)^{|I|}w^{m/Q_I}.
$$
To check the reindexing, a summand originally at $m'$ in $q^{-as}G(t/q^a)$ goes to $m=q^a m'$. Its denominator becomes exactly $m^s$, and its new cutoff is $m\le p^i t$. Each row is a finite sum, so this calculation is valid before taking its uniformly convergent limit.

If $v_{q_j}(m)\ge L_{q_j}+a_j$, pair each subset omitting $j$ with the one including it. Their divisibility conditions coincide. The two exponents of $w$ agree modulo $p-1$ by eventual periodicity, including after division by the other $q_i^{a_i}$. Their signs are opposite, so $A(m)=0$. All nonzero coefficients consequently occur on finitely many rays $m=c r^l$ with $l\ge0$, where the positive multipliers $c$ are coprime to $pr$. Their exponents at each processed prime are bounded. Furthermore:
- $A(m)$ takes values in a finite subset of $\mathbb Z_p$, since the powers of $w$ lie in a finite group and there are at most $2^d$ terms. Fix $V_0$ bounding the valuations of the nonzero values.
- For every $m=r^l$, only the empty subset contributes, so $A(r^l)=w^{r^l}$ is a unit. The differences have retained an entire infinite ray.

## Why a positive-measure zero set is impossible

Choose an integer $B\ge0$ with $(B+1)s>V_0$. The thresholds on the fundamental interval have the form $\tau=c r^l/p^i\in[1,p]$. Distinct thresholds from rows whose indices differ by at most $B$ are separated by a uniform positive distance in $\log t$. To see this, their ratios have the form $(c/c')p^u r^v$ with $|u|\le B$, $v\in\mathbb Z$. For a ratio in $[1/p,p]$, there are finitely many possibilities for $v$, since the allowed $c,c',u$ form finite sets. A ratio equal to one forces equality of row indices by the $p$-valuation, then equality of the two integers. Each integer occurs once per row. [Finite-lattice separation lemma](../NormalityChecker/ThresholdDifferences.lean)

Partition $[1,p)$ into finitely many intervals of smaller log diameter than this separation. Take $t_1<t_2$ in one piece. There is a threshold from the bare ray $r^l$ in $(t_1,t_2)$: the positive multiples of $\log_p r$ are dense modulo one because $p$ and $r$ are distinct primes. Its coefficient is nonzero. Let $i$ be the first row containing any **nonzero** threshold in $(t_1,t_2]$. There is just one at that row and none in the next $B$ rows, by separation. Its contribution to $G(t_2)-G(t_1)$ has valuation at most $is+V_0$. Every remaining row has valuation at least $(i+B+1)s>is+V_0$, also in the limit since this valuation ball is closed. The ultrametric inequality gives $G(t_2)\ne G(t_1)$.

Thus $G$ is injective on each of finitely many intervals and has only finitely many zeros there. This contradicts its positive-measure zero set. The proof shows that the original $Z$ is null. It does not require porosity, comparable adjacent gaps in the original mesh, or independence of reciprocal logarithms for several primes.

## Fixed support versus finite termination

The result implies that the discrepancy certificate for each selected off-base prime tends to zero. It gives no finite depth at which the certificate must vanish. There is a useful precise distinction. On the compact interval $[1,p]$, each finite-level residue function is a step function with finitely many endpoints. Failure at arbitrarily high levels for one fixed support is equivalent to the existence of a zero of a **one-sided** version of $V$: its right-hand value for some $1\le t<p$, or its left-hand limit for some $1<t\le p$. For the forward implication take a subsequence of failing points converging from one side or constant. At each fixed precision its residues eventually equal that side's residue by finiteness of the mesh and nesting. Conversely a zero on one side has a nonempty failing interval on that side at every finite precision. Uniform $p$-adic convergence gives both one-sided limits. The null-set proof also works for left limits using strict row cutoffs. A singleton can still matter for finite termination.

An exhaustive order-one search tested $p=3,5,7$, all base unit residues at each prime, and every set of one to three other primes from $\{2,3,5,7,11,13,17,19\}$. All 756 fixed cases passed by precision eight. The counts first passing at levels 1 through 8 are 589, 85, 50, 22, 5, 2, 2 and 1. The last case has $p=3$, $b\equiv1\bmod3$ and cofactors $2,7,17$. The older precision-12 example is a different fixed support. A fixed unsigned support that fails at every finite precision remains unidentified. The varying-support construction in Phase 10 only supplies arbitrarily large finite depths across a family. [Exact search](../scripts/test_phase_eleven.py) · [Precision-12 example and varying supports](joint-persistent.md#what-finite-refinement-can-detect)

The localized-logarithm manuscript already treats order-one supports wholly coprime to the radix and binary supports containing three. The mixed case above permits any base-prime overlap and every positive order. The reduction from a surviving denominator to local uniformity uses the repository's fixed-prime-support short-orbit estimate. The argument is compatible with abnormal Stoneham sums with different bases or signed weights, for which the unsigned full-support coefficient cancellation used here need not apply. [Earlier finite-prime theorem, §5](https://github.com/CaptainSude/xi-normality/blob/06961817c7f61181ed9a5c73badb8d908d6ccdcc/paper/localized-logarithm-normality.pdf) · [Vandehey](https://arxiv.org/abs/1606.07911) · [Bailey–Borwein](https://doi.org/10.1007/s11139-012-9417-3)
