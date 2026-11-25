# A product of two sparse numerical preservers

For any integer $b\ge2$ and $r\ge2$, there are two explicit irrational elements of $K_b$ whose product is a rational outside $K_b$. Let $A$ be the nonnegative integers whose binary digits are zero in odd-numbered positions, numbering the units bit by zero. Let $B=2A$. Every nonnegative integer has a unique decomposition as $a+c$ with $a\in A,c\in B$, by splitting its binary digits into even and odd positions. Put
$$
 U=\sum_{a\in A}b^{-ra},\qquad V=\sum_{c\in B}b^{-rc}.
$$
Each sum has a term at zero. Apart from that integer, each radix expansion consists of separated ones on a set of counting function $O(\sqrt N)$. Indeed below $4^j$ there are $2^j$ possibilities for the even-position bits and likewise for the odd-position bits. This bound gives vanishing density, infinitely many ones and arbitrarily long runs of zeros. Both numbers are irrational by eventual periodicity of rational digits. Discarding a logarithmic neighborhood before each insertion gives, uniformly in $x$,
$$
 |D_N(x+U)-D_N(x)|+|D_N(x+V)-D_N(x)|
 = O_{b,r}(\log(2N)/\sqrt N).
$$
The real tails on the other positions are bounded by a geometric series in the neighborhood width. [Finite translation bound](../phase18/translations.md#sparse-signed-integers)

Absolute convergence and the unique additive decomposition give $UV=\sum_{n\ge0}b^{-rn}=b^r/(b^r-1)$. Its reduced denominator is coprime to the radix and exceeds $b-1$. Consequently $UV\notin K_b$, although this rational translation preserves normality by rational affine invariance. More precisely its orbit is a translation modulo one of the points represented by the cyclic word of length $r$ with one digit 1 and $r-1$ zeros (the fractional part is $1/(b^r-1)$). Its period is $r$, since $b^j-1<b^r-1$ for $0<j<r$. Its limiting discrepancy equals that of this nontrivial finite cycle, strictly below one. This example separates closure under multiplication from closure under addition and multiplication by scalars in $\mathbb Z[1/b]$. [Scalar classification](geometry.md#asymptotic-kernel-and-arithmetic-operations)

For any established normal number $X$ in this radix, $X+U$ and $X+V$ are explicit normality-preserving decompositions with the stated numerical rates. One may also replace either remainder by any finite sum of copies or radix-primary rational multiples, adjusting the clearing prefix. The product example does not decide whether two members of this sparse subclass can have a normal product.
