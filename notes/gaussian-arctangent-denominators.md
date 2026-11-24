# Binary BBP prefixes for the arctangent of one half and for pi

The angles $`A=\arctan(1/3)`$ and $`C=\arctan(1/7)`$ satisfy $`A+C=\arctan(1/2)`$ and $`2A+C=\pi/4`$. Fix positive integers $`a,c`$ and put $`x=aA+cC`$. There are explicit rational prefixes $`Y_N`$ for $`2^Nx`$, with uniform error $`O_{a,c}(1/N)`$, whose reduced denominators $`Q_N`$ satisfy

```math
\lim_{N\to\infty}\frac{\log Q_N}{N}=\frac23.
```

Thus the same conclusion holds for $`\arctan(1/2)`$ with $`(a,c)=(1,1)`$ and for $`\pi`$ with $`(a,c)=(8,4)`$. The BBP formulas for the two angles and their Machin-type identities are classical. The denominator and error estimates here are paper deductions for truncation at a common binary exponent. [Takahashi, equations (11)–(19)](https://tsukuba.repo.nii.ac.jp/record/2001720/files/RJ_51-1-177.pdf) · [Related prime-survival argument for dyadic logarithms](strided-logarithm.md)

## The two series and the cutoff

For $`t=2,3`$, put $`z_t=(1-i)/2^t`$ and $`e_t(j)=\lceil(2t-1)j/2\rceil`$. The argument of $`1-z_t`$ is $`\arctan(1/(2^t-1))`$. Expand $`\log(1-z_t)`$ and take imaginary parts. For $`j\ge1`$ the integer $`w(j)=-\Im((1-i)^j)/2^{\lfloor j/2\rfloor}`$ repeats the eight values $`1,1,1,0,-1,-1,-1,0`$. Thus

```math
\arctan\frac{1}{2^t-1}
=\sum_{j\ge1}\frac{w(j)}{j2^{e_t(j)}}.
```

The tangent addition formula gives $`\tan(A+C)=1/2`$ and $`\tan(2A+C)=1`$. All angles in both sums are positive and the sums lie below $`\pi/2`$, which proves the two angle identities.

Set $`M_t=\lfloor 2N/(2t-1)\rfloor`$ and write $`b_t(v)=-\sum_{j=1}^v\Im(z_t^j)/j`$. Take $`Y_N=2^N(a b_2(M_2)+c b_3(M_3))`$. The condition $`j\le M_t`$ is exactly $`e_t(j)\le N`$. Every retained denominator after the shift divides the least common multiple $`D_{M_2}`$ of $`1,\ldots,M_2`$, with $`D_0=1`$. Each exponent sequence is strictly increasing. The geometric sum over omitted binary exponents gives

```math
|2^Nx-Y_N|\le\frac{a}{M_2+1}+\frac{c}{M_3+1}.
```

## A residue for the combined numerator

Let $`p`$ be an odd prime with $`p^2>M_2`$. Set $`v_t=\lfloor M_t/p\rfloor`$. After multiplying by $`p`$, precisely the terms with $`p\mid j`$ can contribute modulo $`p`$. In the ring of Gaussian integers modulo $`p`$, raising to the $`p`$th power sends $`i`$ to $`i`$ if $`p\equiv1\pmod4`$ and to $`-i`$ if $`p\equiv3\pmod4`$. This follows from the binomial theorem and holds also when the ring has zero divisors. The rational powers of two in $`z_t`$ are units. Writing $`\chi(p)=(-1)^{(p-1)/2}`$ gives

```math
pY_N\equiv 2^N\chi(p)\big(a b_2(v_2)+c b_3(v_3)\big)\pmod p.
```

This is a test on the combined rational prefix even when both series contribute at $`p`$. If $`Y_N=U_N/Q_N`$ in lowest terms, a nonzero residue means that $`p`$ divides $`Q_N`$ once and the residue equals $`U_N/(Q_N/p)`$ modulo $`p`$.

Every $`b_t(v)`$ is positive for $`v\ge1`$. Indeed its first term is $`1/2^t`$, and with $`B=2^t`$ the sum of the absolute values of all later terms is at most

```math
\frac{|z_t|^2}{2(1-|z_t|)}
=\frac{1}{B(B-\sqrt2)}<\frac1B .
```

Since $`b_t(0)=0`$ and $`a,c>0`$, every short rational on the right of the congruence is strictly positive whenever $`p\le M_2`$.

## Quantitative cancellation bound

In fact $`0\le\log(D_{M_2}/Q_N)=O_{a,c}(N^{2/3})`$. For large $`N`$ put $`K=\lceil N^{1/3}\rceil`$. Primes up to $`K^2`$ cost $`O(K^2)`$ in logarithmic loss. Their first powers cost at most $`\sum_{p\le K^2}\log p=O(K^2)`$ by the Chebyshev bound. All powers after the first, even for the full least common multiple, cost $`O(\sqrt N\log N)`$ by charging at most $`\log N`$ to each prime up to $`\sqrt N`$.

For $`K^2<p\le M_2`$, only the first power of $`p`$ is present and $`1\le v_2\le K`$, $`0\le v_3\le K`$. As $`p`$ increases the pair $`(v_2,v_3)`$ decreases in both coordinates, so at most $`2K+1`$ distinct pairs occur. Each nonzero number $`a b_2(v_2)+c b_3(v_3)`$ has denominator dividing $`8^K D_K`$ and absolute value bounded in terms of $`a,c`$. Its reduced numerator therefore has logarithm $`O_{a,c}(K)`$, using $`\log D_K=O(K)`$. Every lost prime in this range divides one of these numerators. Taking their product bounds the remaining logarithmic loss by $`O_{a,c}(K^2)`$. Finally, the prime number theorem gives $`\log D_{M_2}=M_2+o(M_2)`$, proving the rate.

The calculation supplies both a smaller denominator than the direct Taylor model for $`\arctan(1/2)`$ and a prime-by-prime numerator identity. Controlling the frequency of real binary cylinders for either constant remains open.
