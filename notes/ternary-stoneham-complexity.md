# Repetitions in the ternary expansion of a binary Stoneham number

Let $`\alpha=\sum_{j\ge1}3^{-j}2^{-3^j}`$. For every fixed real $`C\gt 0`$ and every sufficiently large integer $`L`$, the ternary words of length $`L`$ starting at positions $`1`$ through $`1+\lfloor CL\rfloor`$ in $`\alpha`$ are pairwise distinct. In particular, if $`p_3(L)`$ is the ordinary factor complexity, counting every distinct length-$`L`$ word that occurs at least once in this expansion, then

```math
\lim_{L\to\infty}\frac{p_3(L)}{L}=\infty.
```

This is a paper deduction from the Schmidt–Schlickewei Subspace Theorem. Bailey and Borwein discuss base-three normality for this standard series. A convention used in related discussions adds the initial term $`1/2`$. The argument below covers both conventions. The frequency of even a single prescribed ternary digit is a separate question. [Bailey–Borwein, §3, Example 1](https://www.davidhbailey.com/dhbpapers/nonnormality.pdf) · [Related discussion following equation (10)](https://carmamaths.org/resources/jon/pi-monthly.pdf) · [Bilu, Theorems 2.3 and 2.3′](https://www.numdam.org/item/AST_2008__317__1_0/) · [Bugeaud and Kim on word complexity and first repetitions](https://arxiv.org/abs/1510.00282)

## Separation of shifts

Write $`\|x\|`$ for the distance from $`x`$ to the nearest integer. For every $`\epsilon\gt 0`$ there is a $`\delta\gt 0`$ such that, for all sufficiently large integers $`N`$ and all integers $`1\le h\le3^{\delta N}`$,

```math
\|h q\alpha\|\gt 3^{-\epsilon N}
```

for $`q=3^N`$ and for every $`q=3^N-3^m`$ with $`0\le m\lt N`$. The threshold in $`N`$ is uniform in $`h`$ and $`m`$. The approximation exponent with denominators restricted to powers of three is exactly one. Rounding gives error at most $`1/(2\cdot3^N)`$, and only finitely many $`a/3^N`$ approximate $`\alpha`$ within $`3^{-(1+\epsilon)N}`$ for any fixed $`\epsilon\gt 0`$.

Here is how separation gives the stated digit result. If a length-$`L`$ word occurs after both $`m`$ and $`N`$ digits, the fractional parts of $`3^m\alpha`$ and $`3^N\alpha`$ lie in the same interval of length $`3^{-L}`$. Hence $`\|(3^N-3^m)\alpha\|\lt 3^{-L}`$. When $`N\le CL`$, choose $`\epsilon=1/(2C)`$. The separation bound rules out all sufficiently large $`N`$. The finitely many smaller pairs have positive distances because $`\alpha`$ is irrational, as also follows from the pure-power bound with fixed multipliers. Thus $`p_3(L)\ge1+\lfloor CL\rfloor`$ eventually for each $`C`$. Equivalently, the shortest prefix containing two occurrences of any length-$`L`$ word has length growing faster than $`L`$.

There is also a bound on the number of ternary digit changes. A constant run of $`t`$ digits starting at position $`s`$ yields a repeated word of length $`t-1`$ at positions $`s`$ and $`s+1`$. The pair bound gives $`t=o(s)`$ as $`s\to\infty`$. If $`s_j`$ denotes the start of the $`j`$th run, then $`s_{j+1}/s_j\to1`$. Summing $`\log(s_{j+1}/s_j)=o(1)`$ gives $`\log s_j=o(j)`$. Consequently the number of digit changes through position $`N`$, divided by $`\log N`$, tends to infinity.

In Bugeaud’s notation the restriction to denominators of the form *b*ʳ(*b*ˢ − 1) gives *v*′₃(α) = 0. Ordinary factor complexity counts all words appearing anywhere. The argument gives no corresponding superlinear lower bound when only words recurring infinitely often are counted. [Definition of the restricted exponents](https://doi.org/10.1112/jlms/jdp070)

## Two applications of the Subspace Theorem

Use the places $`S=\{\infty,2,3\}`$, with $`|p|_p=p^{-1}`$. We use the following form of the theorem. At each place take a linearly independent system of $`s`$ rational linear forms in $`s`$ variables. For every $`\eta\gt 0`$, the nonzero integer vectors $`x`$ for which the product of all the local absolute values of these forms is at most $`(\max_i|x_i|)^{-\eta}`$ belong to finitely many proper rational subspaces. We will clear powers of two and three from denominators. Multiplying a vector by a common such factor leaves this product unchanged. [Schlickewei's theorem, statement 2.3 in Bilu](https://www.numdam.org/item/AST_2008__317__1_0/)

First, for fixed integers $`a,b`$, with at least one nonzero, we have

```math
v_2(a3^d+b)=o(d)\qquad(d\to\infty).
```

An exact zero can occur at most once. If either coefficient vanishes, the valuation is constant. Otherwise apply the theorem to $`(1,3^d)`$ with coordinate forms at infinity and at 3, and the forms $`X_0,aX_1+bX_0`$ at 2. Their product is $`|a3^d+b|_2`$. If the valuation exceeds any fixed positive multiple of $`d`$ infinitely often, infinitely many points lie on a single rational line through the origin. Their distinct slopes exclude this. A fixed rational pair of coefficients satisfies the same estimate after clearing denominators.

Now suppose the shift bound fails along $`N\to\infty`$. Set $`\lambda=\min(\epsilon,1)/8`$. Fix a positive integer $`R`$ with $`3^R\lambda\ge4`$ and choose $`\delta=\lambda/(4R)`$. For each $`N`$ let $`M=3^J`$ be the largest power of three with $`2^M\le3^{\lambda N}`$. Thus

```math
\frac{\lambda N}{3}\lt M\log_3 2\le\lambda N.
```

Let $`P_j`$ be the sum defining $`\alpha`$ through layer $`j`$, including the optional $`1/2`$ when that convention is used. The integer $`D=3^J2^M`$ clears $`P_J`$. Let $`p`$ be an integer with $`|hq\alpha-p|\le3^{-\epsilon N}`$ and put $`A=D(p-hqP_J)\in\mathbb Z`$. The following $`R`$ layers after multiplication by $`D`$ are

```math
u_i=3^{-i}2^{-(3^i-1)M},\qquad 1\le i\le R.
```

All the omitted positive terms after layer $`J+R`$, multiplied by $`Dhq`$, sum to at most $`h3^N2^{M-3^{R+1}M}`$. This follows by bounding their powers of two by the first omitted one and summing their powers of three. Write $`E=A-hq\sum_{i=1}^R u_i`$. Since $`3^{R+1}M\log_3 2\gt 4N`$, we obtain

```math
|E|\le M3^{-(\epsilon-\lambda)N}
    +3^{(1+\delta+\lambda-4)N}.
```

This gives $`|E|\le3^{-4\lambda N}`$ for all sufficiently large $`N`$. Also $`A\gt 0`$ eventually. Indeed $`q\ge(2/3)3^N`$ and $`u_1=2^{-2M}/3`$, so even the first retained contribution grows exponentially.

Pass to an infinite subsequence of one of the following types. For $`q=3^N`$ use the exponent set $`I=\{N\}`$ with coefficient $`c_N=1`$. For differences with fixed $`d=N-m`$ use $`I=\{N\}`$ with the fixed rational coefficient $`c_N=1-3^{-d}`$. In the remaining case take $`d\to\infty`$, use $`I=\{N,m\}`$ and take $`c_N=1`$, $`c_m=-1`$. In each case $`q=\sum_{e\in I}c_e3^e`$.

Form the vector with coordinates $`A`$ and $`x_{i,e}=h3^e u_i`$. At 2 and 3 use coordinate forms. At infinity replace the first coordinate form by $`A-\sum_{i,e}c_e x_{i,e}`$. The systems are independent and fixed on the chosen subsequence. Each $`3^e u_i`$ is a rational number with numerator and denominator supported on 2 and 3, so its three absolute values multiply to one. The local product for $`h`$ is at most $`h`$, and $`|A|_2|A|_3\le1`$. The full product is consequently at most

```math
3^{-4\lambda N} h^{2R}\le3^{-3\lambda N}.
```

Multiplication by $`3^R2^{(3^R-1)M}`$ clears the vector's denominators and preserves this product. The resulting integer coordinates have ordinary absolute value at most $`3^{K N}`$ for some fixed $`K`$, since $`R`$ is fixed, $`M=O(N)`$, $`h\le3^{\delta N}`$ and $`A`$ is within one of $`hq\sum_i u_i`$. The theorem with, for example, $`\eta=\lambda/K`$ now places infinitely many vectors in one proper rational subspace.

Take a nonzero rational linear relation defining a hyperplane containing that subspace, and clear its coefficients to integers. A relation involving $`A`$ alone is impossible since $`A\gt 0`$. Choose the largest layer $`i`$ having any nonzero coefficient. With one exponent in $`I`$, its contribution has 2-adic valuation $`v_2(h)-(3^i-1)M+O(1)`$. With two exponents the contribution is

```math
h3^{m-i}2^{-(3^i-1)M}(a3^d+b)
```

for some fixed integers $`a,b`$ not both zero. By the first application of the theorem its valuation is $`v_2(h)-(3^i-1)M+o(N)`$, since $`d\to\infty`$ and $`d\le N`$. This valuation is negative by a linear margin, already for $`i=1`$, because $`v_2(h)\le\delta N\log_2 3`$ and $`2M\gt (2\lambda/3)N\log_2 3`$. It is also smaller by a linear margin than the valuations of all earlier nonzero layers. The integer multiple of $`A`$ has nonnegative valuation whenever it is nonzero. The unique term of least valuation cannot sum to zero. This contradicts the relation and proves separation.

The Subspace Theorem gives no explicit starting digit here. The argument controls repetitions on a scale proportional to the starting positions. A positive lower density of digit changes, a strict upper discrepancy below one and ternary normality remain unresolved by this estimate.
