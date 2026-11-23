# Two positive normal summands with an irrational nonnormal sum

Fix an integer base $b\ge2$ and a real $\eta<1$. There is a positive integer $d$ such that, writing $l=2d+1$ and taking $c$ to be the odd part of $b^{2d}+1$, the two numbers
$$
x=T_{b,c,1},\qquad y=lT_{b,c,l},\qquad
T_{b,c,m}=\sum_{j\ge0}\frac{b^{-mc^j}}{mc^j}
$$
are positive and individually normal in base $b$. Their sum is irrational and nonnormal in that base. For every fixed $r\ge1$, the upper limiting frequency of the length-$r$ all-zero word in $x+y$ exceeds $\eta$. The choice of $d$ is independent of $r$. The Lean theorem is `severe_normal_summands`. [Formal statement and proof](../NormalityChecker/StonehamComponents.lean)

## Normality of an individual summand

The following argument works for any odd $c>1$ coprime to $b$ and any $m\ge1$. Put $q=c^k$, let $t$ be the order of $b$ modulo $q$, and write $C=b^{\varphi(c)}-1$. Then $q\le Ct$. Indeed, put $g=b^{\varphi(c)}$ and take any prime $p\mid c$. Euler's theorem gives $p\mid g-1$, and $q\mid g^t-1$. Lifting the exponent at this odd prime gives $v_p(g^t-1)=v_p(g-1)+v_p(t)$. Thus $q\mid Ct$. [Period bound](../NormalityChecker/StonehamOrder.lean)

Write $e_q(z)=\exp(2\pi i z/q)$. For $T\le\min(t,q)$ and $z\bmod q$, let $S(z)=\sum_{i<T}e_q(zb^i)$. The $T$ residues $b^i$ are distinct, so character orthogonality gives
$$
\sum_{z\bmod q}|S(z)|^2=qT\le q^2.
$$
Fix an integer $h\ne0$, a positive integer $H$, and a unit $A\bmod q$. For all sufficiently large $k$, the $H$ residues $hAb^j$ with $0\le j<H$ are distinct. Multiplication by $A$ is injective, and the finitely many nonzero integer differences $h(b^i-b^j)$ all have magnitude less than $q$. Hence one of these residues has $|S(hAb^j)|\le q/\sqrt H$. Shifting the $T$ exponents by $j$ changes their sum by at most $2j$, giving
$$
|S(hA)|\le q/\sqrt H+2H.
$$
Every prefix of length at most $q$ splits into at most $C$ segments of length at most $t$. Each segment starts with another unit in place of $A$. First choosing $H$ large and then letting $k$ grow proves $o(q)$ cancellation uniformly in the unit and the prefix length. The frequency $h$ is fixed throughout. [Finite-orbit proof](../NormalityChecker/StonehamOrbit.lean)

Let $W=mT_{b,c,m}$. Split the positions from $mq$ through $mcq-1$ into cells $[uq,(u+1)q)$ for $m\le u<mc$. At the beginning of a cell, the shifted sum of the terms with $j\le k$ is $A/q$ with $A$ coprime to $c$. Clearing denominators at the newest insertion gives a numerator congruent to $b^{uq-mq}$ modulo $c$. At offset $i$ this prefix becomes $Ab^i/q$. The remaining shifted tail is at most $1/((c-1)q)$ throughout the cell, since every power of $b$ in the shifted tail has nonpositive exponent. Character values for $b^{uq+i}W$ and $Ab^i/q$ therefore differ by at most $2\pi |h|/((c-1)q)$. The orbit estimate controls every partial cell. Summing geometrically over all preceding scales gives vanishing Fourier averages at every nonzero frequency. Weyl's criterion proves normality of $W$, and the integer-dilation theorem gives normality of $T_{b,c,m}$ as well. [Series and tail](../NormalityChecker/StonehamComponents.lean) · [Cell summation](../NormalityChecker/ScaleTransfer.lean) · [Dilation](../NormalityChecker/Dilation.lean)

## Resonance of the sum

For $1\le m<l<c$ and $c\mid b^{l-m}+1$, lifting the minus-one congruence makes every completed pair integral after shifting on $[lc^k,c^{k+1})$. The remaining positive tail is at most $2/((c-1)c^k)$. For any fixed $r$, eventually every start in each such interval gives $r$ zero digits. Up to $N=c^{k+1}$ these disjoint intervals have limiting proportion $(c-l)/(c-1)$. Strict positivity of the tail also proves irrationality, since shifts of a rational of denominator $D$ have nonzero distances from integers of at least $1/D$. [Resonance and irrationality](../NormalityChecker/GeneralResonance.lean) · [Frequency bound](../NormalityChecker/ResonantDensity.lean)

For the stated choice $m=1$, $l=2d+1$, the odd integer $c$ divides $b^{2d}+1$ and is coprime to $b$. When $b$ is odd, $b^{2d}+1\equiv2\pmod4$, so at most one factor of two needs to be removed. Since $c\ge(b^{2d}+1)/2$, the bound $1-2d/(c-1)$ tends to one. The previous two arguments now apply to the same summands. For instance, $b=10$, $c=101$, $m=1$, $l=3$ gives a lower bound of $98/100$ for every fixed zero-block length.

Individual normality belongs to the classical Stoneham theory. The development above supplies the period, cancellation, and transfer arguments inside the project. The priority of the quantitative statement for sums has not been established. [Bailey and Crandall, *Random Generators and Normal Numbers*](https://doi.org/10.1080/10586458.2002.10504704)
