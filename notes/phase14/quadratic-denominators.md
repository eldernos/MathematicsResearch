# Exact denominators for parameter-two quadratics

Let *b* ≥ 3 be an odd integer and let *A*, *B*, *C*₀ be integers with *A* ≠ 0. Set
$\alpha=\sum_{j\ge1}2^{-j}b^{-2^j}$. At cutoff *n* the shifted prefix of $A\alpha^2+B\alpha+C_0$ is

$$
R_n=A\sum_{2^i+2^j\le n}\frac{b^{n-2^i-2^j}}{2^{i+j}}
    +B\sum_{2^i\le n}\frac{b^{n-2^i}}{2^i}+C_0 b^n.
$$

Both indices are positive. The double sum counts both orders. Write $q(n)$ for the positive reduced denominator, including $q(n)=1$ for an integer. Take $v_2(2)=1$, $v_2(0)=+\infty$, $|x|_2=2^{-v_2(x)}$, and $[r]_+=\max(0,r)$, with $[-\infty]_+=0$. Define $s=v_2(b^2-1)-1\ge2$ and $a=v_2(2A)$.

**Upper-shell theorem.** There is an explicit $\kappa\in\mathbb Q_2$ depending only on $b,A,B$ such that for every $k\ge1$ and every $3\cdot2^{k-1}\le n<2^{k+1}$,

$$
q(n)=q_k=2^{[k-a-s-v_2(k-\kappa)]_+}.
$$

Thus $q_k=1$ if $k=\kappa$. If $\kappa$ is algebraic over $\mathbb Q$, the upper denominators tend to infinity. For every nonnegative integer *h*, distinct indices $i<j$ with $q_i,q_j\le2^h$ and $i>a+s+h$ satisfy $2^{i-a-s-h}\mid j-i$. On the lower half the denominator is eventually $2^{2k-2-v_2(A)}$. The formula for every earlier cutoff, including a possible tie, is given below. Lean checks the exact upper formula for the displayed prefix, the exact lower and initial reductions, algebraic upper growth and quantitative separation. [Prefix and denominators](../../NormalityChecker/ParameterTwoQuadratic.lean) · [Algebraic growth and separation](../../NormalityChecker/ParameterTwoQuadraticHeight.lean)

## The limit, its intercept and the error

Work in $\mathbb Q_2$. For $j\ge1$ put $\delta_j=(b^{-2^j}-1)/2^j$. Since $b^2$ is one modulo eight and $b$ is a unit, $v_2(\delta_1)=s$. Squaring $1+2^j\delta_j$ gives

$$
\delta_{j+1}=\delta_j+2^{j-1}\delta_j^2.
$$

Inductively $v_2(\delta_j)=s$. The step has valuation $j-1+2s>s$ and these step valuations strictly increase. Completeness gives a limit $\lambda$. The tail $\lambda-\delta_j$ has the valuation of its first summand,

$$
v_2(\lambda)=s,\qquad v_2(\delta_j-\lambda)=j-1+2s.
$$

Set $d_j=\delta_j-\lambda$. The series $\sum d_j$ converges, with valuation $2s$ because its first term has strictly smaller valuation than every subsequent term. Define

$$
C=\lambda+\sum_{j\ge1}d_j,\qquad
T_k=\sum_{j=1}^k\delta_j+\delta_k.
$$

Then $v_2(C)=s$ and
$$
T_k=k\lambda+C+E_k,\qquad E_k=d_k-\sum_{j>k}d_j,\qquad
v_2(E_k)=k-1+2s.
$$

The tail after $d_k$ has strictly larger valuation. In particular the proposed lower bound is sharp at every index. In Lean, `delta b j` is $\delta_{j+1}$ and `cancellation b j` is $T_{j+1}$. Theorems `slope_valuation`, `delta_error_norm` and `affine_error_norm` use these actual series. [Convergence and sharp error](../../NormalityChecker/ParameterTwoQuadraticLimit.lean)

## Why the affine error disappears after reduction

Let $L_j=2^{-j}b^{-2^j}$, $S_k=\sum_{j=1}^k L_j$ and $H_k=1+\sum_{j=1}^k\delta_j$. Summing $L_j=2^{-j}+\delta_j$ gives $S_k=H_k-2^{-k}$. On the upper interval, the permitted square is the complete $k$ by $k$ square minus $(k,k)$. Indeed the largest other insertion, for $k\ge2$, occurs at $2^k+2^{k-1}$. For $k=1$ the only pair is the omitted diagonal. Hence $b^{-n}R_n=A(S_k^2-L_k^2)+B S_k+C_0$. In particular

$$
b^{-n}R_n=
 A(H_k^2-\delta_k^2)+BH_k+C_0
 -2^{-k}(2A+B+2AT_k).
$$

The first three terms are 2-adic integers. The actual prefix $R_n$ is dyadic by its finite definition and $b^n$ is a 2-adic unit. Consequently $q(n)=\max(1,|R_n|_2)$. Terms of norm at most one can be removed inside this maximum. Now define

$$
\kappa=-\frac{2A+B+2AC}{2A\lambda}.
$$

The numerator of the pole is $2A\lambda(k-\kappa)+2AE_k$. Since $v_2(2AE_k)=a+k-1+2s\ge k$, reduction gives exactly the upper-shell formula. Equivalently $q_k=\max(1,2^k|2A\lambda(k-\kappa)|_2)$. This norm form covers a vanishing affine factor, a vanishing finite numerator $2A+B+2AT_k$, and $R_n=0$ itself. When $k=\kappa$ the finite pole numerator equals $2AE_k$, which has the stated finite valuation. The two numerators need only agree modulo $2^k$. The 2-adic identity here is for the pole of the actual finite shifted rational. [Phase 13 finite identity](../phase13/reviews/symmetric-degree.md#quadratic-projections-with-equal-valuations) · [Kernel proof of the affine formula](../../NormalityChecker/ParameterTwoQuadratic.lean)

One has $\kappa\in\mathbb Z_2$ exactly when $v_2(2A+B)\ge a+s$. In the complementary case, $v_2(k-\kappa)=v_2(\kappa)=v_2(2A+B)-a-s$ for every integer $k$. This recovers $q_k=2^{[k-v_2(2A+B)]_+}$. For integral $\kappa$, indices $k\equiv\kappa\pmod{2^m}$ occur for every *m* and arbitrarily far out. They permit unbounded loss relative to *k*. Bounded **denominators** require precision increasing almost point for point with the index.

## Lower half, ties and initial cutoffs

At $n=0,1$ the rational prefix is integral. At $n=2,3$ the square is empty and the only nonconstant term is $B b^{n-2}/2$, giving denominator $2^{[1-v_2(B)]_+}$. This includes the first upper cutoff $n=3$ also covered by the theorem.

Fix $k\ge2$ and $2^k\le n<3\cdot2^{k-1}$. Write the shifted square and linear prefixes in lowest terms as $U_n/2^{2k-2}$ and $V_n/2^k$. Both $U_n,V_n$ are odd. The former follows from the Phase 13 lower-half square theorem. For the latter, $2^k b^n S_k=\sum_{j=1}^k 2^{k-j}b^{n-2^j}$ has exactly one odd summand. Put $e_A=2k-2-v_2(A)$ and $e_B=k-v_2(B)$, allowing $e_B=-\infty$ for $B=0$. [Exact square numerator and denominator](../../NormalityChecker/ParameterTwoSquareProfile.lean) · [Linear numerator](../../NormalityChecker/ParameterTwoQuadratic.lean)

- If $e_A\ne e_B$, then $q(n)=2^{[\max(e_A,e_B)]_+}$. The two summands have different valuations.
- If $e_A=e_B=e\le0$, both terms are integral and $q(n)=1$.
- If $e_A=e_B=e>0$, write $A'=A/2^{v_2(A)}$ and $B'=B/2^{v_2(B)}$. Then $q(n)=2^{[e-v_2(A'U_n+B'V_n)]_+}$. This includes zero sum and allows dependence on the cutoff within the tied shell.

Lean also verifies a single gcd formula for all three lower cases. With $N=A U_n+B V_n2^{k-2}$ it gives $q(n)=2^{2k-2}/\gcd(2^{2k-2},|N|)$, including $N=0$. The constant contributes an integer throughout. For $B\ne0$ the unique possible tie index is $k=2+v_2(A)-v_2(B)$, provided it is at least two. For all $k>2+v_2(A)$ the lower denominator is exactly $2^{2k-2-v_2(A)}$, uniformly in $B,C_0,n$. For instance at $b=3$, $A=B=1$, $k=2$, $n=4$, the prefixes are $1/4$ and $19/4$ and their sum is 5. For $A=1,B=-2$, $k=3$, $n=12$, the respective prefixes are $7315/4$ and $249399/8$, giving the integer $-60521$ before the constant term.

## Algebraic indices and separation

Suppose $\kappa\in\mathbb Z_2$ is algebraic over $\mathbb Q$. Clear denominators of a nonzero annihilating polynomial to get $P(X)=\sum_{r=0}^d a_r X^r\in\mathbb Z[X]$. Put $H=\sum_r|a_r|$. For an integer $k\ge1$ with $P(k)\ne0$, subtraction of powers gives
$$
P(k)=(k-\kappa)\sum_{r=1}^d a_r\sum_{m=0}^{r-1} k^{r-1-m}\kappa^m.
$$
The second factor is integral at two. The nonzero ordinary integer $P(k)$ has $2^{v_2(P(k))}\le |P(k)|\le Hk^d$. Thus
$$
v_2(k-\kappa)\le v_2(P(k))\le \log_2(Hk^d),\qquad
q_k\ge\frac{2^{k-a-s}}{Hk^d}.
$$
Only finitely many integer roots were excluded, including $k=\kappa$ if it is a positive integer. The nonintegral case already has constant $v_2(k-\kappa)$. This proves growth for algebraic $\kappa$ of every degree. The normality consequence uses the separate dynamical criterion for growing upper denominators and the lower-half estimate.

For $q_i,q_j\le2^h$ with $i<j$, the formula forces $v_2(i-\kappa)\ge i-a-s-h$ and $v_2(j-\kappa)\ge j-a-s-h$. The ultrametric inequality gives $2^{i-a-s-h}\mid j-i$ whenever the exponent is positive, hence $j-i\ge 2^{i-a-s-h}$. In any window of fixed length there is therefore eventually at most one such index. More generally, if $0<\theta<1$ and $q_i\le2^{\theta i}$, $q_j\le2^{\theta j}$, the same proof gives $v_2(j-i)\ge(1-\theta)i-a-s$. These bounds concern the **shell index**. A single upper half shell still spans $2^{i-1}$ digit cutoffs. [Height and spacing proofs](../../NormalityChecker/ParameterTwoQuadraticHeight.lean)

## What the logarithm identifies for the polynomial X² − 2X

Here $A=1,B=-2$, so $\kappa=-C/\lambda$. The ordinary 2-adic exponential and logarithm are inverse on $4\mathbb Z_2$ and $1+4\mathbb Z_2$. The series for $\log(1+t)$ gives it valuation $v_2(t)$ when $v_2(t)\ge2$. Hence $u=\tfrac12\log(b^{-2})$ has valuation $s$. Then $b^{-2^j}=\exp(2^ju)$ and division of its exponential series by $2^j$ gives $\delta_j\to u$. Thus $\lambda=u$ with the same choice of logarithm for both odd residue classes modulo four. Substituting the exponential series into the intercept gives

$$
\kappa=-1-\sum_{r=2}^{\infty}
  \frac{2^{r-1}}{(1-2^{r-1})r!}\lambda^{r-1}.
$$

Indeed $\delta_j-\lambda=\sum_{r\ge2}2^{j(r-1)}\lambda^r/r!$. Since $v_2(r!)\le r-1$, each summand has valuation at least $(j-1)(r-1)+rs$. This lower bound tends to infinity off finite sets, allowing the two orders of summation. Summing first over *j* gives the displayed geometric factor. The coefficients of $\lambda^{r-1}$ are integral at two because $1-2^{r-1}$ is odd and $v_2(r!)\le r-1$. The coefficient of $\lambda$ is $+1$. Consequently $\kappa=-1+\lambda\pmod{2^{2s}}$ and $v_2(\kappa+1)=s$. For example $b=3$ gives $\lambda\equiv5900$, $C\equiv2044$, $\kappa\equiv15595\pmod{2^{16}}$. These residues follow by iterating the recurrence at extra precision before division by $\lambda$.

The two-logarithm estimate of Bugeaud and Laurent bounds the valuation of nonzero differences of powers of fixed algebraic numbers under their independence and local-unit hypotheses. Its inputs carry algebraic heights. In this problem the quantity to bound is $k\lambda+C$. Here $\exp(\lambda)$ is the unique one of $b^{-1},-b^{-1}$ congruent to one modulo four. The identity $v_2(\exp(t)-1)=v_2(t)$ for $t\in4\mathbb Z_2$ gives $v_2(k\lambda+C)=v_2(\exp(\lambda)^k-\exp(-C))$. A two-logarithm argument would therefore need arithmetic control of $\exp(-C)$. The formula above expresses $C$ by a convergent nonlinear series in $\lambda$ and gives no identification of $\exp(C)$ as an algebraic number or of $C$ as a fixed linear combination of logarithms of algebraic numbers. Applying a bound for $v_2(k\lambda)$ loses the summand that creates the cancellation. [Y. Bugeaud and M. Laurent, “Minoration effective de la distance p-adique entre puissances de nombres algébriques,” Journal of Number Theory 61 (1996), 311–342](https://www.sciencedirect.com/journal/journal-of-number-theory/vol/61/issue/2)

Truncation gives a specific height obstruction. Set $C_m=\lambda+\sum_{j=1}^m(\delta_j-\lambda)$ for $m\ge1$. Then $v_2(C-C_m)=m+2s$, while $k\lambda+C_m=(k-m+1)\lambda+r_m$ with $r_m=\sum_{j=1}^m\delta_j\in\mathbb Q$. The reduced denominator of $r_m$ is exactly $b^{2^m}$. Each summand has odd denominator dividing this integer, and for any prime $p\mid b$ the last summand uniquely has the smallest valuation $-2^m v_p(b)$. Replacing $C$ by $C_m$ to precision $k-O(1)$ thus requires $m\ge k-O_b(1)$, with the logarithm of the height of $r_m$ already at least $2^m\log b$. An estimate treating $r_m$ as fixed would miss this growth. The cited logarithm estimate gives no bound here forcing $k-v_2(k-\kappa)\to\infty$ for $X^2-2X$. Algebraicity of this $\kappa$ and that growth both remain open in this analysis.

An independent finite check started the two shifted prefixes at zero. Each step multiplied the preceding rational by *b* and added each newly inserted term $2^{-i}$ or $2^{-i-j}$ at its defining position. For all $0\le n<512$, $b\in\{3,5,7,9,15\}$ and $(A,B)\in\{(1,0),(1,-2),(1,1),(-2,4),(8,1),(6,-4),(16,0)\}$, the direct reduced denominator agreed with the piecewise formulas in all 17,920 cases. The upper prediction used the finite recurrence for $\delta_j$ with $\lambda,C$ computed modulo $2^{64}$, reducing $2A+B+2A(k\lambda+C)$ only as far as the cutoff required. The logarithm comparison and its series expansion above are paper deductions.

<details>
<summary>Reproduce the finite check with Python 3</summary>

The integer in the upper prediction is known modulo $2^{64}$, which suffices because each tested shell index is at most eight. The lower prediction uses the gcd formula with the separately reduced linear and square numerators.

```python
from collections import defaultdict
from fractions import Fraction
from math import gcd

mod = 2**64
coefficients = [(1, 0), (1, -2), (1, 1), (-2, 4), (8, 1), (6, -4), (16, 0)]
checks = 0
for b in (3, 5, 7, 9, 15):
    d = ((1 - b*b) // 2) * pow(b*b, -1, mod) % mod
    deltas = []
    for j in range(1, 66):
        deltas.append(d)
        d = (d + 2**(j-1) * d*d) % mod
    slope = d
    intercept = (slope + sum(u - slope for u in deltas)) % mod

    single, pair = defaultdict(Fraction), defaultdict(Fraction)
    for i in range(1, 9):
        single[2**i] += Fraction(1, 2**i)
        for j in range(1, 9):
            pair[2**i + 2**j] += Fraction(1, 2**(i+j))
    linear = square = Fraction(0)
    for n in range(512):
        linear = b*linear + single[n]
        square = b*square + pair[n]
        k = n.bit_length() - 1
        for A, B in coefficients:
            if n < 2:
                q = 1
            elif n < 4:
                q = 2 // gcd(2, B)
            elif n < 3 * 2**(k-1):
                numerator = A*square.numerator + B*linear.numerator * 2**(k-2)
                denominator = 2**(2*k-2)
                q = denominator // gcd(denominator, numerator)
            else:
                pole = 2*A + B + 2*A*(k*slope + intercept)
                q = 2**k // gcd(2**k, pole)
            assert (A*square + B*linear + 7*b**n).denominator == q
            checks += 1
assert checks == 17920
```

</details>
