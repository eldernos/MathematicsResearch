# Corrected binary shifts of the two-stride logarithm

Write $m_2=\lfloor N/2\rfloor$, $m_3=\lfloor N/3\rfloor$ and $L_M=\mathrm{lcm}(1,\ldots,M)$, with $L_0=1$. The two correction orders $r_2,r_3$ may be chosen independently at every starting position. Put $M=\max(m_2+r_2,m_3+r_3)$ and $D=\max(r_2,2r_3)$.

**Finite theorem (Lean).** There is an explicit rational $Y$ for $2^N\ln2$ whose reduced denominator divides $3^D L_M$. Write $B(m,j)=m!j!/(m+j+1)!$. Its unwrapped error is bounded by
$$
|2^N\ln2-Y|\le
2^{1+(N\bmod 2)}3^{-r_2}B(m_2,r_2)
+2^{N\bmod 3}9^{-r_3}B(m_3,r_3).
$$
The right side multiplied by $2^i$ controls the same model after $i$ further binary shifts. The previously conjectured bounds for coverage $N/2,N,2N$ all hold. The improved asymptotic budgets below follow on paper by Stirling's formula and the prime number theorem. They bound a common denominator of the corrected model. [Lean model, denominator and error](../NormalityChecker/CorrectedStrides.lean) · [Exact cost certificates](../scripts/corrected_strides.py)

## Integral and common denominator

For a stride $k$ with $a=2^k$, sign $\sigma=\pm1$ and $m=\lfloor N/k\rfloor$, the tail of the series with coefficients $\sigma^{j-1}/(ja^j)$, after the shift $2^N$, is
$$
2^{N-km}\sigma^m\int_0^1\frac{t^m}{a-\sigma t}\,dt.
$$
Expand the geometric series under the integral (absolute convergence on [0,1]). Around $t=1$ use $a-\sigma t=(a-\sigma)+\sigma(1-t)$. The first $r$ corrections inside this integral are $(-\sigma)^j B(m,j)/(a-\sigma)^{j+1}$ for $0\le j<r$. The residual is $(-\sigma)^r/(a-\sigma)^r$ times the same integral with the extra numerator factor $(1-t)^r$. Its absolute value is at most $B(m,r)/|a-\sigma|^r$, since $|a-\sigma t|\ge1$. In a direct computation the minima of the denominators improve the two error terms by factors of 3 and 8 respectively.

The Lean proof uses a signed radix $A=4$ or $-8$. It starts the rational prefix at zero and applies $R_{m+1}=A R_m+1/(m+1)$. The two zeroth integrals are $\log(4/3)$ and $\log(8/9)$, and twice the first minus the second is $\ln2$. This also fixes the alternating sign and the multiplicative phase at incomplete strides. The identity
$$
B(m,j)=\sum_{\ell=0}^j\frac{(-1)^\ell\binom j\ell}{m+\ell+1}
$$
shows that its denominator divides $L_{m+j+1}$. Thus every correction fits on the asserted single common denominator. No product of the two least common multiples is required.

## Linear forward coverage

Let $i\le\lfloor\alpha N\rfloor$, $m=\lfloor\beta N\rfloor$, $r=\lceil\rho N\rceil$ and $d=|a-\sigma|$. For fixed $\beta,\rho>0$, put
$$
F(\beta,\rho,d)=(\beta+\rho)\log(\beta+\rho)
-\beta\log\beta-\rho\log\rho+\rho\log d.
$$
Stirling's formula gives $d^{-r}B(m,r)=O(N^{-1/2}e^{-NF})$. Floors and ceilings change the constant by a bounded factor. Consequently equality $F=\alpha\log2$ already gives an error tending to zero **including the last shift**. Increasing $\rho$ increases $F$ strictly. The logarithm of the displayed common denominator divided by $N$ tends to
$$
C=\max(1/2+\rho_2,1/3+\rho_3)+\max(\rho_2,2\rho_3)\log3.
$$

| Forward length | Certified proportions for strides 2 and 3 | Improved upper rate | Requested upper rate | Original one-stride beta budget | Original full-degree Chebyshev budget |
| --- | --- | --- | --- | --- | --- |
| $N/2$ | 0.08857, 0.07169 | 0.746090 | 0.751 | 1.104829 | 1.543184 |
| $N$ | 0.22365, 0.16931 | 1.095663 | 1.099 | 1.293816 | 2.086368 |
| $2N$ | 0.58202, 0.40077 | 1.962602 | 1.969 | 2 | 3.172735 |

The improved upper rates are rounded upwards. To verify the strict entropy comparisons exactly, clear the rational proportions with a common denominator $u$. Set $m=u\beta$, $r=u\rho$, $h=u\alpha$ and compare $(m+r)^{m+r}d^r$ with $2^h m^m r^r$ in integers. The program bounds $\log3$ by the series $2\,\mathrm{atanh}(1/2)$ and a rational upper tail. The proposed proportions also give strict positive margins. The limiting optimal cost **within this beta envelope and common-denominator estimate** is found by solving the two scalar equalities separately. The resulting numerical rates are approximately 0.746074, 1.095644 and 1.962576.

For the original beta model take $\beta=1,d=1$ and common denominator $L_{N+r}$. The Chebyshev comparison uses the Phase 10 bound $1/((N+1)T_r(3))$ with common denominator $T_r(3)L_{N+r}$. Thus $r/N=\alpha\log2/\log(3+\sqrt8)$ suffices there. These comparisons concern the guaranteed error and stated denominator bounds of the existing models. Cancellation in a reduced fraction, or a different error estimate for a kernel, can change the comparison. [Original beta integral](../NormalityChecker/LogShadowIntegral.lean) · [Chebyshev bound](../NormalityChecker/ChebyshevModels.lean)

## Prime powers and the extra factor of three

Set $K=3^D$ and use the integer coefficients $u_j$ in $KY=\sum_{j\le M}u_j/j$. The raw positive and alternating prefixes supply their usual coefficients multiplied by $K$. Each correction contributes the signed binomial coefficients above multiplied by the integer $K/(A-1)^{j+1}$, its sign and the external stride multiplier. Let $B=KL_M Y$, an integer. For $p^v\Vert L_M$, the following computes $B\bmod p^v$ from just the multiples of $p$:
$$
 B\equiv (L_M/p^v)\sum_{j\le M,\,p\mid j}
 u_j\,p^{v-v_p(j)}(j/p^{v_p(j)})^{-1}\pmod {p^v}.
$$
Indeed terms with $p\nmid j$ vanish after clearing. For $p\ne3$ this determines the entire surviving exponent, $\max(0,v-v_p(B))$. If it is positive and $Y=A/q$ in lowest terms, reduction of $B=(KL_M/q)A$ gives the corresponding congruences for the actual reduced numerator after removing common factors. In particular a unit residue gives the full $p^v$ in $q$. For prime powers in any rational reduction, the exact general rule is $v_p(q)=\max(0,v_p(KL_M)-v_p(B))$.

The large correction factor has a cheap, separate residue. Modulo $K$, the whole raw prefix drops out of $B$. For each correction with signed multiplier $\lambda$, add
$$
 \lambda\,(-1)^j\,\frac{K}{(A-1)^{j+1}}\,\bigl(L_M B(m,j)\bigr)\pmod K.
$$
Both parenthesized divisions in the algorithm are exact integers. This computation uses $r_2+r_3$ beta terms. It can be combined with every large odd prime power other than 3 by CRT; the ordinary $3$-part of $L_M$ can be left among the unknown lifts. This is particularly important on long windows, where charging the entire extra $3^D$ as unknown would make the residual grid exponentially larger. [CRT implementation and independent rational cross-checks](../scripts/corrected_strides.py)

## Actual rates for the uncorrected logarithms

For the uncorrected two-stride model, **Lean now proves** $\log\mathrm{den}(Y_N)/N\to1/2$. The proof uses the actual recurrence, not just $L_{\lfloor N/2\rfloor}$. Its periodic integer weight is $4\mathbf1_{2\mid j}+3\mathbf1_{3\mid j}-6\mathbf1_{6\mid j}$. For $p>3$ this weight is invariant under $j\mapsto pj$. When $N<p^2$, the difference $Y_N-2^{N-\lfloor N/p\rfloor}Y_{\lfloor N/p\rfloor}/p$ is integral at $p$, by Fermat's theorem. The short prefix is strictly positive at every index at least two. For each fixed $k$, every prime in $(N/k,N/2]$ therefore survives for sufficiently large $N$. The prime number theorem gives the lower bound and the common denominator the upper. The broader optimality statement among all finite dyadic logarithm identities uses Bang's primitive-divisor theorem in the Phase 10 paper proof. [Kernel limit](../NormalityChecker/StrideDenominatorRate.lean) · [Representation class and optimality proof](strided-logarithm.md#why-half-is-optimal-in-this-class)
