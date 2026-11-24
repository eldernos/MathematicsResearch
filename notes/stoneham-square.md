# Binary normality of the Stoneham square

**Theorem.** Let

$$
\alpha=\sum_{j=1}^{\infty}\frac{1}{3^j 2^{3^j}}.
$$

Then $\alpha^2$ is normal in base 2. Its true shifted rational prefix at digit $n$ is

$$
R_n=\sum_{i,j\ge1,\ 3^i+3^j\le n}
       \frac{2^{n-3^i-3^j}}{3^{i+j}}.
$$

Write $q_n$ for its reduced positive denominator. For $n\ge81$ one has $n^2<243q_n$ and $q_n\le n^2$. Lean proves the exact table below, the initial exceptions, both quadratic bounds, the true shifted-tail limit and binary normality. [Lean statements and proofs](../NormalityChecker/StonehamSquare.lean)

| Digit positions, for each integer k ≥ 4 | Exponent of 3 in the reduced denominator |
| --- | ---: |
| From 3ᵏ up to 3ᵏ + 3ᵏ⁻² | 2k − 2 |
| From 3ᵏ + 3ᵏ⁻² up to 3ᵏ + 3ᵏ⁻¹ | 2k − 3 |
| From 3ᵏ + 3ᵏ⁻¹ up to 2·3ᵏ | 2k − 1 |
| From 2·3ᵏ up to 3ᵏ⁺¹ | 2k |

Each interval includes its left endpoint and excludes its right endpoint. Here are all earlier reduced denominators.

| Digit positions | Reduced denominator |
| --- | ---: |
| [0, 6) | 1 |
| [6, 12) | 9 |
| [12, 18) | 27 |
| [18, 30) | 81 |
| [30, 36) | 9 |
| [36, 54) | 243 |
| [54, 81) | 729 |

## Exact ternary cancellation

Write $k=\lfloor\log_3 n\rfloor$. Throughout its scale every ordered pair with both indices at most $k-1$ is present, because $2\cdot3^{k-1}<3^k$. A new pair must have one index equal to $k$. Its other index $j$ first enters at $3^k+3^j$. Thus the entire second interval has precisely the old pairs and the two new arms through $j=k-2$.

Let $D$ be the largest present sum of indices $i+j$. The integer $3^D R_n$ is a sum of powers of three times $2^{n-3^i-3^j}$. Every $3^i+3^j$ is a multiple of six, so the binary factor is congruent to the same unit $2^n$ modulo nine for every included pair. Modulo three the normalized numerator therefore counts the top layer, up to a unit. Modulo nine it counts that layer plus three times the layer immediately below.

- Before $3^k+3^{k-2}$, the sole pair of largest degree is $(k-1,k-1)$. Its degree is $2k-2$.
- At $3^k+3^{k-2}$, the degree-$2k-2$ layer acquires $(k,k-2)$ and its transpose. The degree-$2k-3$ layer consists of $(k-1,k-2)$, $(k,k-3)$ and their transposes. All four are present at the left endpoint. Removing the common binary unit gives $3+3\cdot4=15\equiv6\pmod9$. Exactly one factor of three cancels.
- At $3^k+3^{k-1}$ the two new pairs of degree $2k-1$ give a unit modulo three. At $2\cdot3^k$ the single diagonal pair of degree $2k$ gives a unit.

The hypothesis $k\ge4$ matters. At $k=3$ the would-be pair $(k,k-3)$ uses index zero, which the series omits. The normalized numerator now vanishes modulo nine. Exact reduction gives $R_{30}=16952434/9$, $R_{35}=542477888/9$ and $R_{36}=29293805954/243$. Lean checks all 81 initial positions by kernel reduction. An independent rational recurrence $R_n=2R_{n-1}+\sum_{3^i+3^j=n}3^{-i-j}$ also reproduces both tables. [Exact profile and finite checks](../NormalityChecker/StonehamSquare.lean)

## The true tail and digit normality

The summands of $\alpha$ are positive and absolutely summable, so multiplying the series gives the sum over ordered pairs. For each fixed pair, its contribution to $2^n\alpha^2-R_n$ vanishes once its location is reached. Before then its shifted contribution is at most $3^{-i-j}$, and the sum of these majorants is finite. Dominated convergence for series gives $2^n\alpha^2-R_n\to0$. In particular, an insertion arbitrarily close to $n$ is covered by the same proof.

Use scales $9^h\le n<9^{h+1}$ and clean blocks of length $3^h$. Before the end of such a scale each index is at most $2(h+1)$, so at most $4(h+1)^2$ ordered pairs can insert. Removing blocks that meet insertion locations costs a vanishing proportion. On every other block the rational prefixes are successive doublings of the starting prefix. Their starting denominators are powers of three, grow uniformly to infinity, and are bounded by $(3^h)^6$ for $h\ge1$. The fixed-support short-orbit estimate and the true tail bound now give the Weyl criterion along all prefixes. [Arithmetic normality certificate](../NormalityChecker/ArithmeticCertificate.lean) · [Fixed-support short-orbit theorem](../NormalityChecker/SmoothOrbit.lean) · [Application to the square](../NormalityChecker/StonehamSquare.lean)
