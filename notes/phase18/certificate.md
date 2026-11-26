# From a grouped series to an interval-count certificate

Let $b\ge2$ be an integer, and let $(a_i)$ be a countable absolutely summable real family with total $x$. Partition its indices into disjoint groups $G_j$, finite or countable. Suppose $\sum_{i\in G_j}a_i=c_j b^{-m_j}+e_j$, with absolute convergence of the grouped models and errors. Equal exponents may be combined. Then
$$
 x=\sum_j c_j b^{-m_j}+z,\qquad z=\sum_j e_j.
$$
Fubini for absolutely summable families proves the identity even when observation cutoffs cross arbitrarily many groups. Small unshifted $|e_j|$ alone gives no bound on $T^n z$. Use a mean-displacement estimate for $z$, a scale-dependent tail estimate, or modeled values for $z$ jointly with the other terms. [Translations](translations.md) · [Dynamic transfer](summation.md)

For each $N>0$ take disjoint intervals of shifts $B_i\subset[0,N)$ (including truncated intervals). On $B_i$ model the orbit by consecutive shifts of a rational $y_i$; the start of the block is its zeroth shift. Allow $E$ exceptions among the covered samples and require pointwise circle error at most $\epsilon$ on the others. Let $U$ count all uncovered samples. If $\Delta_i$ bounds the extreme discrepancy of the rational orbit over **this** block length, then
$$
 D_N(x)\le \frac{U+E+\sum_i |B_i|\Delta_i}{N}+2\epsilon .
$$
Indeed, expand each test arc by $\epsilon+h$ on both sides, compare the good counts to the expanded model counts, add the exceptions, and let $h$ decrease to zero. Complementary arcs treat deficits. Uncovered samples cost at most one each. This proof permits any arithmetic certificate for $\Delta_i$. A complete rational period of length $P$ with discrepancy $d$ gives count error at most $|B_i|d+\min(P,|B_i|)$, including unfinished periods. Alternatively the fixed-support short-orbit theorem gives arbitrarily small discrepancy uniformly when denominators tend to infinity and are bounded by a fixed power of growing block length. [Repository block theorem](../../docs/results.md#ac-01) · [Short orbits](../../docs/results.md#ac-04)

**A necessary bound.** Suppose also that at $H_Q(N)$ positions some given model is rational of reduced denominator at most $Q$, and differs from the sample there by at most $\epsilon$, apart from $E$ exceptions. Let $F_Q$ consist of the reduced circle fractions of denominator at most $Q$, with $0$ counted once. Some center then accounts for at least $(H_Q(N)-E)/|F_Q|$ good samples. An arc of length at most $2\epsilon+2h$ contains them, even at zero by using the circle. Hence
$$
 D_N(x)\ge\frac{H_Q(N)-E}{N|F_Q|}-2\epsilon .
$$
If the error tends to zero in density, normality requires $H_Q(N)/N\to0$ for every fixed $Q$. Conversely suppose that for every $\eta>0$ one can choose a fixed $Q$ such that, for all sufficiently large $N$, all but $H_Q(N)+\eta N$ positions can be covered by blocks with $\Delta_i\le\eta$ and with at most $\eta N$ exceptions of radius $\eta$. Then $D_N(x)\le H_Q(N)/N+5\eta$. For the special case where the exceptional bounded-denominator positions all model zero and the rest supplies uniform counts up to $o(N)$, the upper and lower bounds match with $|F|=1$. The all-prefix estimate and its quantitative cubic implementation appear in the [programming proof](programming.md).

**Why the hypotheses matter.** A rational model $1/p^{\lfloor\log_p(n+2)\rfloor}$ at each shift approximates the orbit of zero with growing denominator on one prime; changing the numerator independently at each step destroys the required orbit relation. Fixed bounded denominators can also have different discrepancies: in base two, states zero and $1/3$ each have bounded denominators everywhere, but their discrepancy limits are 1 and $2/3$.

There is a separate obstruction for raw truncations. Write zero as the sum of pairs $+2^{-k}/3$ inserted at $k$ and $-2^{-k}/3$ inserted at $2k$, $k\ge1$. At the second insertion the raw coefficient of $2^{-2k}$ is $-2^k/3$. The series is absolutely convergent and each completed pair is zero. At the raw cutoff $n$, the shifted value of the unfinished pairs is $(2^{\lceil n/2\rceil}-1)/3$. Its circle distance from zero is $1/3$ for $n\equiv1,2\bmod4$. Thus even exact, harmless completed groups need not justify using the **raw prefix** as the model at intermediate shifts. The exact grouped model for the full sum is zero at every shift.

For a positive example of artificial complexity, the finite geometric grouping in the [principal family](principal.md) can introduce new raw denominator primes at unboundedly many lengths even when the resulting grouped coefficients are all one. For classical Taylor terms a different cost occurs: positive dyadic groups require future multiples of the original odd denominator primes. These obstructions concern particular representations. [Logarithm groups](classical.md) · [Least omitted prime in localized sums](summation.md#what-happens-on-approaching-the-full-logarithm)
