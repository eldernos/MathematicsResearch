<img src="assets/icon.svg" width="64" height="64" alt="">

# NormalityChecker

[![Lean verification](https://github.com/eldernos/MathematicsResearch/actions/workflows/lean.yml/badge.svg)](https://github.com/eldernos/MathematicsResearch/actions/workflows/lean.yml)

Lean 4 proofs about the binary expansion of $\log 2$, the prime factors that survive in its shifted rational approximations, and an explicit infinite series that fails binary normality. The project grew out of the [shared research conversation](https://chatgpt.com/share/6b04aebe-d930-83e9-9175-772054b7d221).

## A binary normality checker for finite sums

For any finite set of positive indices and any rational coefficients, Lean now proves a necessary-and-sufficient test for binary normality of $F=\sum a_m T_m$. Pick $S$ at least the largest index. On each of the finitely many cells $S\le u<3S$, compute $j_m=\lfloor\log_3\lfloor u/m\rfloor\rfloor$ and $H_u=\sum_m a_m(-1)^m/(m3^{j_m})$. Then $F$ is binary normal exactly when every $H_u$ is nonzero.

The consequences include binary normality of each $T_m$, binary normality of every ordered finite partial sum of the logarithmic decomposition, and the equivalence
$$
T_1+aT_2\text{ is binary normal}\quad\Longleftrightarrow\quad a\notin\{2/3,2\}\quad (a\in\mathbb Q).
$$
The unweighted sum $T_{20}+T_{28}+T_{35}$ is nonnormal. The finite test is executable and its correctness theorem refers directly to overlapping digit blocks. [Mathematical proof](notes/finite-sums.md) · [Lean classification and checker](NormalityChecker/FiniteClassification.lean)

```lean
import NormalityChecker
open NormalityChecker
#eval binaryNormalTest {1, 2} (fun _ => 1)         -- true
#eval binaryNormalTest {20, 28, 35} (fun _ => 1) -- false
```

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
| How are the components related to $\log 2$? | Summing $T_m$ over positive $m$ indivisible by three gives exactly $\log 2$. For each $K\ge1$, using **all** such indices $m\le K$, the sum $\sum f(m)/m$ is nonzero for every choice of odd integers $f(m)$. This proves the parity step used by the finite classification. [OrderedComponents.lean](NormalityChecker/OrderedComponents.lean) |

## Finite sums and incomplete orbits

For $T_1+aT_2$, Lean proves that binary normality requires $a\notin\{2/3,2\}$. The coefficient $2/3$ pairs the $j$-th term of $T_2$ with the $(j+1)$-st term of $T_1$. For $k\ge3$, every start in $[3^k,2\cdot3^k)$ has next block `00`. This accounts for at least half the starts in a prefix ending at $2\cdot3^k$. [Resonance.lean](NormalityChecker/Resonance.lean)

For every $q=3^k$ with $k\ge2$, $3\nmid A$, and every interval of exponents $[u,u+N)$, the checked incomplete-sum bound is
$$
\left|\sum_{n=u}^{u+N-1}\exp(2\pi i A2^n/q)\right|\le 5\sqrt q(1+\log q).
$$
With $r=\lceil k/2\rceil$, cubing shows $2^{2\cdot3^{r-1}}=1+c3^r$ with $c\equiv1\pmod3$. The square of $c3^r$ vanishes modulo $q$. Splitting the exponent into stride classes therefore gives geometric series modulo $m=3^{k-r}$. Multiplication by a unit permutes the powers of two over each period. The geometric bounds sum to at most $m(1+\log m)$ per period of row indices, by the harmonic sum estimate. The final incomplete row of exponents costs at most one stride. The restriction $k\ge2$ matters for an estimate uniform in $N$ since the complete sum modulo three need not vanish. [Linearization](NormalityChecker/Linearization.lean) · [Interval estimate](NormalityChecker/OrbitSum.lean)

## Polylogarithms and separated positions

The exact prime criteria now cover all integer radices $b\ge2$ and all positive orders $s$. The checked loss bound is $4s(21+7s+b)n^{2/3}$ for $n\ge b^3$. The short proof note gives the exceptional-prime rule, the $s=0$ case, and links to the Lean statements. [Arithmetic note](notes/denominators.md)

For any starting index and lag, the rational recurrence satisfies
$$
0\le R_{n+r}-2^rR_n
=\sum_{j=1}^r\frac{2^{r-j}}{n+j}
\le\frac{2^r-1}{n+1}.
$$
Writing $e(t)=\exp(2\pi i t)$, the joint character $e(h R_n+g R_{n+r})$ differs from $e((h+2^r g)R_n)$ by at most $2\pi |g|(2^r-1)/(n+1)$. This controls each fixed lag. The factor $2^r$ limits its use at growing lags. Lean also proves that vanishing of the Cesàro means of $e(h R_n)$ for every signed odd $h$ suffices for binary normality of $\log 2$. The proof uses a one-step shift to remove factors of two and Weyl’s criterion to pass to all overlapping digit blocks. [Correlations](NormalityChecker/Correlations.lean) · [Weyl criterion](NormalityChecker/Analysis/Weyl.lean)

## Open proof obligations

The finite classification holds for each fixed family. Passing to the infinite sum for $\log 2$ requires bounds uniform as that family grows with the digit position. The proof for fixed $M$ allows its cutoff to depend on every nonzero cell coefficient. A coefficient with a large power of three in its numerator postpones the point at which the orbit estimate is effective.

For $\log 2$, the open input is cancellation of the odd-frequency means. The sequence $1/Q_n$ already shows why denominator growth alone cannot supply it. Fixed-lag correlations describe a constraint on any candidate distribution. They give no decay by themselves. Neither $\log 2$ nor $\pi$ has been classified here.

## Reproduce and review

Lean and Mathlib are pinned to v4.36.0. With Elan installed, run from the repository root:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get $(sed -nE 's/^(public )?import (Mathlib\.[A-Za-z0-9_.]+)$/\2/p' NormalityChecker/*.lean NormalityChecker/Analysis/*.lean | sort -u)
scripts/verify.sh
```

The verification script builds the library, audits the transitive axiom dependencies of the headline theorems, then replays every project module with `leanchecker`. The audit permits only `propext`, `Classical.choice`, and `Quot.sound`. GitHub Actions runs the same checks on pushes and pull requests. The original verified baseline is tagged `research-checkpoint-1`. [Axiom audit](Audit.lean) · [CI workflow](.github/workflows/lean.yml)

The project is an AI-assisted formalization of questions raised in the linked conversation. Lean checks the declarations and their dependencies. The correspondence between the definitions and the intended mathematics, and questions of priority, remain matters for human review. Original contributions are MIT-licensed. The port of Trevor Morris’s Weyl criterion retains Apache-2.0 and identifies the upstream revision in its header. [MIT license](LICENSE) · [Weyl license](NormalityChecker/Analysis/LICENSE-Weyl) · [Upstream Weyl criterion](https://github.com/gotrevor/normal-numbers/blob/6260625c6836d8bb172da4b011e089f63a728c41/src/NormalNumbers/WeylCriterion.lean)
