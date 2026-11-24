# Two prime-adic digits of logarithm and arctangent prefixes

Let $`L_k=\log(2^k/(2^k-1))`$ for $`k\ge1`$ and let $`\theta=\arctan(1/2)`$. The usual Taylor series give rational prefixes for binary shifts of each number. Fix an odd prime $`p`$. In the window of $`p`$ consecutive prefixes that contain exactly one summand with denominator divisible by $`p`$, the first $`p`$-adic digit after multiplying by $`p`$ is geometric. The next digit satisfies a uniform counting bound. In any $`T`$ consecutive positions of the window, any prescribed residue of the multiplied prefix modulo $`p^2`$ occurs $`O(T^{2/3})`$ times. The same bound holds when the geometric contribution is removed and just the residual digit modulo $`p`$ is prescribed. The implied constants are absolute, including as $`k`$ varies. These are paper results for the rational prefixes.

## Prefixes and the distinguished summand

Use the following parameters. Each $`Y_m`$ approximates the target multiplied by the shift in its row.

| Target | Shift | $`B`$ | $`u`$ | $`a`$ | $`c`$ |
| --- | --- | --- | --- | --- | --- |
| $`L_k`$ | $`2^{km}`$ | $`2^k`$ | $`1/B`$ | 1 | $`1/B`$ |
| $`\theta`$ | $`2^{2m}`$ | 4 | $`-1/4`$ | 2 | $`1/2`$ |

```math
Y_m=cB^m\sum_{j=0}^{m-1}\frac{u^j}{aj+1}.
```

Indeed $`-\log(1-1/B)=\sum_{j\ge0}B^{-(j+1)}/(j+1)`$ and $`\theta=\tfrac12\sum_{j\ge0}(-1/4)^j/(2j+1)`$. Set $`s=(p-1)/a`$. For $`s+1\le m\le s+p`$, only $`j=s`$ has $`p\mid aj+1`$ and $`as+1=p`$. Put $`G_m=cB^m u^s`$ and $`Z_m=Y_m-G_m/p`$. Both $`G_m`$ and $`Z_m`$ have denominators prime to $`p`$, with $`G_m`$ a unit. The identity

```math
pY_m=G_m+pZ_m
```

determines the leading residue from $`G_m`$ modulo $`p`$ and the full residue modulo $`p^2`$ from $`G_m`$ modulo $`p^2`$ and $`Z_m`$ modulo $`p`$. In particular, if $`Y_m=A_m/Q_m`$ is reduced, then $`p`$ divides $`Q_m`$ exactly once and $`pY_m=A_m/(Q_m/p)`$. Thus the left side is the reduced numerator multiplied by the inverse of its prime-to-$`p`$ denominator modulo $`p^2`$.

## A bound for every prime and every target residue

Fix $`0\lt r\lt p`$ and two target residues $`w,z`$. Among indices $`m,m+r`$ in the window, at most $`r`$ values of $`m`$ give that ordered pair in the logarithm case and at most $`2r`$ in the arctangent case. This holds both for $`pY_m`$ modulo $`p^2`$ and for $`Z_m`$ modulo $`p`$.

To prove it, write $`\rho=Bu`$, which is 1 for the logarithm and $`-1`$ for the arctangent. Define the rational function

```math
F_r(X)=\sum_{j=0}^{r-1}\frac{u^j}{a(X+j)+1}.
```

The difference over $`r`$ successive truncations is $`Y_{m+r}-B^rY_m=cB^r\rho^m F_r(m)`$. None of the denominators of $`F_r(m)`$ vanishes modulo $`p`$ at an admissible $`m`$. Also $`G_{m+r}=B^rG_m`$, so the same difference formula holds for $`Z_m`$. For the two residues modulo $`p^2`$, the congruence requires $`z-B^r w=0`$ modulo $`p`$. When this holds, divide $`z-B^r w`$ by $`p`$ using integer lifts of the residues modulo $`p^2`$. Its residue modulo $`p`$ is independent of the lifts. The difference formula now prescribes a value of $`F_r(m)`$ modulo $`p`$ for each possible sign of $`\rho^m`$. For the two residues of $`Z_m`$ modulo $`p`$, the difference formula prescribes the value directly.

For each fixed value $`t`$, multiply $`F_r(X)-t`$ by the product of its $`r`$ linear denominators over the field with $`p`$ elements. The resulting polynomial has degree at most $`r`$. At the root $`-1/a`$ of its first denominator, its value is $`a^{r-1}(r-1)!`$, nonzero because $`r\lt p`$. Hence it has at most $`r`$ roots. All admissible $`m`$ are distinct modulo $`p`$. Summing over the possible signs proves the pair bound.

For a prescribed residue, partition the $`T`$ positions into intervals of at most $`H+1`$ consecutive positions, with $`1\le H\lt p`$. Each occurrence after the first in an interval forms a returning pair at some gap $`1\le r\le H`$. The number of occurrences is therefore at most

```math
\left\lceil\frac{T}{H+1}\right\rceil+H(H+1).
```

The logarithm permits $`H(H+1)/2`$ for the last term. Choosing $`H=\max(1,\lfloor T^{1/3}\rfloor)`$ proves the stated bound. The logarithm prefix at binary position $`km+t`$, for fixed $`0\le t\lt k`$, is $`2^tY_m`$. The arctangent prefix at odd position $`2m-1`$ is $`Y_m/2`$. Either factor is invertible at $`p`$, so the counting bounds extend to each fixed phase.

## Bounds on the real shifts from the literature

Rivoal's Theorems 1 and 2 give a different estimate directly on $`L_k`$. Write $`B=2^k`$ and $`\Lambda_k=\Lambda(1,B,1)`$ in his notation. For each sufficiently large $`k`$, every $`\eta\gt 0`$ and all sufficiently large $`m`$, one has $`\|B^mL_k\|\ge B^{-(\Lambda_k-1+\eta)m}`$, where $`\|x\|`$ is the distance to the nearest integer. His bound gives

```math
\Lambda_k-1\le\frac{2+\log 2}{k\log 2}+O(k^{-2}).
```

The paper also gives $`\Lambda_k\lt 2`$ for $`B\ge12`$, hence for $`k\ge4`$. For an arbitrary binary position $`n`$, apply the bound at $`m=\lceil n/k\rceil`$ and use $`\|2^{km}L_k\|\le2^{km-n}\|2^nL_k\|`$. For fixed $`k`$, the rounding factor is bounded and can be absorbed by increasing $`\eta`$. Thus the same exponential rate applies at every binary shift. Bugeaud and Kim's Theorem 2.2 also applies to $`L_k=\log(1+1/(2^k-1))`$. In every integer base and for all sufficiently large $`k`$ depending on $`\eta\gt 0`$, the lower limit of the ratio of length-$`L`$ word complexity to $`L`$ is at least $`9/8-\eta`$. [Rivoal, Theorems 1–3 and the remark after Theorem 3](https://doi.org/10.4171/RMI/519) · [Bugeaud and Kim, Theorem 2.2](https://arxiv.org/abs/1510.00282)

Bashmakova and Salikhov proved a finite upper bound for the ordinary irrationality exponent of $`\theta`$ using symmetrized integrals. Bai's 2026 preprint reports the upper bound $`8.585166\ldots`$. For any exponent $`\mu`$ above a proved upper bound, taking the denominator $`2^n`$ gives $`\|2^n\theta\|\ge2^{-(\mu-1)n}`$ eventually. Such estimates constrain individual binary runs. The modular counting theorem above concerns the residues of the actual Taylor prefixes. Obtaining a positive lower density of binary transitions from these results remains open. [Bashmakova and Salikhov](https://www.mathnet.ru/eng/cheb836) · [Bai, preprint](https://arxiv.org/abs/2608.19782)
