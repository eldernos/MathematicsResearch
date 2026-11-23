<img src="assets/icon.svg" width="64" height="64" alt="">

# NormalityChecker

Lean 4 proofs about the binary expansion of $\log 2$, the prime factors that survive in its shifted rational approximations, and an explicit infinite series that fails binary normality. The project grew out of the [shared research conversation](https://chatgpt.com/share/6b04aebe-d930-83e9-9175-772054b7d221).

## The two arithmetic milestones

Write

$$
A_n=\sum_{j=1}^{n}\frac{1}{j2^j},\qquad
R_n=2^n A_n,\qquad
Q_n=\operatorname{den}(R_n),\qquad
D_n=\operatorname{lcm}(1,\ldots,n).
$$

1. **Exact cancellation.** For every odd prime $p$ and every $a\ge1$ with $p^a\le n<p^{a+1}$, let $k=\lfloor n/p^a\rfloor$. Then $p^a\mid Q_n$ if and only if $p$ does not divide the reduced numerator of $A_k$. For example, $Q_{10}=63$. To see why a short prefix suffices, clear denominators with $D_n$ and reduce modulo $p$. Only indices divisible by $p^a$ can contribute. On those indices Fermat's theorem gives $2^{jp^a}\equiv2^j\pmod p$. [PrimeCancellation.lean](NormalityChecker/PrimeCancellation.lean)
2. **Quantitative loss.** For $n\ge8$ the checked bound is $0\le\log(D_n/Q_n)\le116n^{2/3}$. For a cutoff $K\ge2$ with $n\le K^3$, three copies of $D_{K^2}$ cover all powers of primes at most $K^2$. Each larger prime occurs to exponent at most one. If it cancels, the first theorem puts it in a numerator of $A_1,\ldots,A_K$. Chebyshev's upper bound gives a total log loss of at most $29K^2$. Taking $K=\lceil n^{1/3}\rceil$ gives the stated inequality. Mathlib's prime number theorem for $D_n$ then gives $\log Q_n/n\to1$. [DenominatorGrowth.lean](NormalityChecker/DenominatorGrowth.lean)

## Which digit questions the proofs settle

| Question | Lean result |
| --- | --- |
| How can approximations certify normality in an integer base $b\ge2$? | If $b^n x-u_n\to0$, normality of $x$ is equivalent to uniform distribution of $u_n$ modulo one. The proof starts from frequencies of overlapping digit blocks and handles wraparound at integer boundaries. [Distribution.lean](NormalityChecker/Distribution.lean) |
| What does this give for $\log 2$? | $R_0=0$, $R_{n+1}=2R_n+1/(n+1)$ and $0\le 2^n\log2-R_n\le1/(n+1)$. Binary normality is equivalent to uniform distribution of this exact rational recurrence. [LogTwo.lean](NormalityChecker/LogTwo.lean) |
| Does the proposed cancellation example work? | For $T_m=\sum_{j\ge0}2^{-m3^j}/(m3^j)$, the sum $T_1+2T_2$ fails binary normality. For every $k\ge2$, every start $2\cdot3^k\le n<3^{k+1}$ has next block `00`. That gives at least $1/3$ of the first $3^{k+1}$ starts, above the required $1/4$. [Resonance.lean](NormalityChecker/Resonance.lean) |
| How are the components related to $\log 2$? | Summing $T_m$ over positive $m$ indivisible by three gives exactly $\log 2$. For each $K\ge1$, using **all** such indices $m\le K$, the sum $\sum f(m)/m$ is nonzero for every choice of odd integers $f(m)$. This proves the parity step in the proposed finite classification. [OrderedComponents.lean](NormalityChecker/OrderedComponents.lean) |

## Where the attempt stops

**For the rational recurrence**, arbitrarily large reduced denominators alone permit concentration. Lean proves that $1/Q_n$ has the very same reduced denominator at every index and tends to zero. The recurrence adds more information. If $s+2$ consecutive fractional parts of $R_n$ lie in $[0,1/4)$ starting at $n\ge1$, then $4\cdot2^s<n+1$. On such a run the recurrence doubles the fractional part and adds a positive term without wrapping. The length bound leaves open the total number of separated visits. A concrete next target is to bound the discrepancy of the number of visits to $[0,1/4)$ among the first $N$ indices. This single interval is already a necessary test for uniform distribution. [Run bound](NormalityChecker/LogTwo.lean) · [Denominator obstruction](NormalityChecker/DenominatorGrowth.lean)

**For finite sums of components**, normality of the individual summands, the proposed general classification, and normality of every ordered partial sum are outside the checked conclusions here. The next analytic step is to turn a nonzero value of the proposed piecewise resonance function into cancellation on partial doubling orbits modulo powers of three, uniformly over prefix endpoints for each fixed finite sum. The cited two-Stoneham-sum project proves a theorem for a different parameter family and develops incomplete-orbit estimates relevant to this step. Applying a fixed-family result to $\log 2$ would also require control while the number of components grows. The normality questions for $\log 2$ and $\pi$ remain open. [Two-sum theorem and proof guide](https://github.com/CaptainSude/Stoneham-sum-normal/blob/main/theorem-guide.md)

## Reproduce

Run from this directory with Elan installed. The toolchain and Mathlib are pinned to v4.36.0.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build
lake env lean Audit.lean
for source in NormalityChecker/*.lean; do
  module=$(basename "$source" .lean)
  lake env leanchecker "NormalityChecker.$module" || exit 1
done
```

The kernel replay checks the project's compiled declarations. The audit checks the transitive axiom dependencies of 18 main results and fails if it finds anything beyond `propext`, `Classical.choice`, and `Quot.sound`. [Audit.lean](Audit.lean)

Created in [T3 Code](https://t3.codes).
