# Prime cancellation in truncated polylogarithms

For integers $b\ge2$, $s\ge0$, set
$$
A(n)=\sum_{j=1}^n\frac1{j^s b^j},\quad R(n)=b^n A(n),\quad
Q(n)=\operatorname{den}(R(n)),\quad D(n)=\operatorname{lcm}(1,\ldots,n).
$$
Use $D(0)=1$. The common denominator of the shifted terms divides $D(n)^s$. The case $b=2,s=1$ gives the shifted logarithm series.

## Which prime powers survive?

Let $s,a\ge1$, $p$ prime, $p^a\le n<p^{a+1}$ and $k=\lfloor n/p^a\rfloor$. Write the numerator of a rational in reduced form. Then

| Condition | Equivalent to $p^{as}\mid Q(n)$ |
| --- | --- |
| $p\nmid b$ | $p\nmid \operatorname{num} A(k)$ |
| $p\mid b$ | $p^a\mid n$ |

Write $D(n)=p^a C$, where $p\nmid C$. The integer $S=D(n)^s R(n)$ is a sum of $b^{n-j}(D(n)/j)^s$. The entire power $p^{as}$ survives reduction precisely when $p\nmid S$. Terms with $p^a\nmid j$ vanish modulo $p$. At $j=p^a i$, the factor $D(n)/j=C/i$ and $1\le i\le k<p$.

If $p\nmid b$, Fermat gives $b^{p^a i}\equiv b^i\pmod p$. Hence $S\equiv b^n C^s A(k)\pmod p$, where the denominator of $A(k)$ is invertible modulo $p$. If $p\mid b$, the factor $b^{n-j}$ kills every earlier index and the last term survives precisely for $p^a\mid n$. When $s=0$, every shifted sum is integral and $Q(n)=1$. The prime tests classify survival of the **full** available power. Partial survival can occur. [Lean statements and proofs](../NormalityChecker/Polylog.lean)

## How much can cancel?

For $n\ge b^3$ the proved uniform inequality is
$$
0\le \log\frac{D(n)^s}{Q(n)}
\le 4s(21+7s+b)n^{2/3}.
$$
In particular the loss is $O_{b,s}(n^{2/3})$ for each fixed radix and order. The original proof for $b=2,s=1$ retains its sharper constant $116$. [General bound](../NormalityChecker/PolylogGrowth.lean) · [Logarithm bound](../NormalityChecker/DenominatorGrowth.lean)

Take $K=\lceil n^{1/3}\rceil$. For $p\le K^2$, the exponent of $p$ in $D(n)$ is at most three times its exponent in $D(K^2)$. Indeed, if $l=\lfloor\log_p K^2\rfloor\ge1$, then $n\le K^3\le K^4<p^{2(l+1)}$, and $2l+1\le3l$. Thus $D(K^2)^{3s}$ covers every small-prime loss.

For $K^2<p\le n$, one has $n<p^2$ and $p>b$. A loss from the top power $p^s$ forces $p$ to divide a short numerator with $1\le k=\lfloor n/p\rfloor\le K$. Consequently
$$
D(n)^s\mid Q(n) D(K^2)^{3s}
\left(\prod_{k=1}^K|\operatorname{num} A(k)|\right)^s .
$$
Here the outer exponent $s$ covers even the complete loss of $p^s$. Every short numerator is positive and at most $D(k)^s b^k$, since this is a common denominator for $A(k)$ and $A(k)\le1$. Chebyshev's estimate in Mathlib gives $\log D(t)\le7t$, so the logarithm of the product before raising it to $s$ is at most $(7s+b)K^2$. Combining the two allowances and using $K\le2n^{1/3}$ gives the bound.

The Chebyshev estimate and the prime number theorem used in the original logarithmic asymptotic come from Mathlib. The specialization and polylogarithmic deductions above have Lean proofs in this repository. Priority in the literature has not been established. [Chebyshev functions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Chebyshev.html) · [Weak PNT](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/WeakPNT.html)
