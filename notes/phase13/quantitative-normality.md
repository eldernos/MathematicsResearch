# Power-saving discrepancy for Stoneham polynomials in their defining radix

**Theorem (paper deduction from the denominator theorem and Vandehey).** Fix an integer $b\ge2$, an odd prime $p\nmid b$, an integer $e\ge1$ and a rational polynomial $P$ of degree $d\ge1$. Set $x=P(\alpha_{b,p^e})$, where $\alpha_{b,c}=\sum_{j\ge1}c^{-j}b^{-c^j}$. Let $D_N(x;b)$ be the supremum over $0\le u<v\le1$ of the absolute difference between $v-u$ and the proportion of $0\le n<N$ with $\{b^n x\}\in[u,v)$. For every $N\ge2$,

```math
D_N(x;b)\le C N^{-\delta_d},
\qquad \delta_d=\frac{1}{2(2^{d+1}-2)} .
```

The constant $C$ is computable from the fixed data. The same conclusion holds for a rational linear combination of products of $\alpha_{b^{m_i},p^{e_i}}$ with fixed positive integers $m_i,e_i$, provided exactly one nonzero monomial has highest degree $d$. Thus the theorem includes every quadratic $P$ with nonzero leading coefficient, of either sign. These estimates control every digit-word frequency because each digit cylinder is an interval. [Denominator bounds](../../NormalityChecker/StonehamPolynomialPrefix.lean) · [Survival under lower-degree perturbations](../../NormalityChecker/StonehamPolynomialNormal.lean) · [Standard generators and rational polynomials](../../NormalityChecker/StonehamPolynomial.lean)

Sharper rates from the proof follow below. Here $L_N=1+\log N$. In degree one the displayed bound also holds for rational affine images of a single standard generator with **any** $c\ge2$ coprime to $b$.

| Degree | Normalized discrepancy bound | Example |
|---|---|---|
| One | $O(N^{-1/2}L_N^2)$ | $\alpha_{2,3}$ |
| Two | $O(N^{-1/6}L_N^2)$ | $\alpha_{2,3}^2$ |
| Three | $O(N^{-1/14}L_N^{51/28})$ | $\alpha_{2,3}^3$ |

In using equation (12) of Vandehey’s preprint, take the product over primes dividing the actual reduced modulus, with the factor for 4 only when 4 divides that modulus. A frequency may remove an allowed prime entirely. Taking the maximum over the finitely many supports contained in the original support makes the constants uniform. [Independent source check and correction](reviews/quantitative-coverage.md) · [Review of all-prefix coverage](reviews/quantitative-and-mixed.md)

## Prefix arithmetic, including rational coefficients

In a degree-$a$ monomial, write $q_i=p^{e_i}$, $s(j)=\sum_i m_iq_i^{j_i}$ and $w(j)=\prod_i q_i^{-j_i}$ for ordered tuples of positive indices. Its shifted prefix $R_n$ is the sum of $w(j)b^{n-s(j)}$ over $s(j)\le n$. For a constant monomial set $R_n=b^n$. Extend $R_n$ by linearity. Multiple tuples at one position all contribute. The zero-index Lean model gives these same positive-index factors after replacing $m_i$ by $m_iq_i$ and dividing the value and prefix by $q_i$ in each factor.

For an integer combination $Y$ in the theorem, write $q_n$ for the reduced denominator of $R_n(Y)$. It is a power of $p$. For all sufficiently large $n$ it satisfies $c_1 n^d\le q_n\le c_2 n^d$, with $c_1,c_2>0$ depending on the data. Indeed, for $k=\lfloor\log_p n\rfloor$ the top prefix retains $p^{dk-O(1)}$. Its nonzero multiplier costs at most its own $p$-valuation, whereas all lower terms together have denominator dividing $p^{(d-1)k}$, up to fixed factors from the indexing convention. At late cutoffs their pole orders are strictly smaller. The upper bound follows by clearing $p^{dk}$ for positive indices. For the single degree-one generator with arbitrary $c$, if $c^k\le n<c^{k+1}$ then its denominator is exactly $c^k$ for $k\ge1$. After clearing it, the last insertion contributes a unit modulo $c$ and all earlier insertions contribute multiples of $c$. A fixed nonzero integer multiplier costs at most its absolute value. [Kernel denominator survival](../../NormalityChecker/StonehamPolynomialNormal.lean) · [Exact binary-square profile and the bounds $n^2/243<q_n\le n^2$ for $n\ge81$](../../NormalityChecker/StonehamSquare.lean)

For rational coefficients choose a common positive denominator $D$. Factor it as $D_b D_0$, where every prime divisor of $D_b$ divides $b$ and $\gcd(D_0,b)=1$. Choose $t\ge0$ with $D_b\mid b^t$. Write $x'=b^t x=Y/D_0$ with integral coefficients in $Y$. For every test interval, shifting the orbit by $t$ changes the count through $N$ by at most $t$. It therefore suffices to treat $x'$. If $Q_n$ is the denominator of $R_n(Y)/D_0$, then

```math
q_n\mid Q_n,\qquad Q_n\mid D_0q_n .
```

The first divisibility follows by multiplying back by $D_0$. All $Q_n$ have support in a fixed finite set $S$ of primes coprime to $b$, and $Q_n\asymp n^d$. For degree one on a composite axis use the primes dividing $cD_0$ instead. This argument handles the constant coefficient as well as coefficient denominators with base-prime factors. Wall's qualitative affine invariance alone gives no numerical discrepancy estimate. [Lean divisibility statements](../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean)

## Uniform real tail and insertion count

For each nonempty monomial let $W=\sum_i m_i$ and $G=\prod_i(1-q_i^{-1})^{-1}$. Whenever $s(j)>n$, some index $i$ has $Wq_i^{j_i}\ge n+1$. If every index failed this test, then $s(j)\le W\max_i q_i^{j_i}<n+1$. In coordinate $i$ the sum of $q_i^{-j_i}$ subject to the test is at most $W/((n+1)(1-q_i^{-1}))$, by summing a geometric tail from its first admissible exponent. In all other coordinates sum the entire geometric series. The factor $b^{n-s(j)}$ is at most one. Consequently, at **every** cutoff, including the position immediately before an insertion,

```math
0\le b^n M-R_n(M)\le\frac{a W G}{n+1}.
```

The same proof permits zero-index factors and the constant case has zero error. Summing with absolute coefficient weights gives $|b^n x'-R_n(x')|\le K/(n+1)$. The Lean theorem gives the coarser explicit numerator $a(2\max(1,W))^a$ for the zero-index convention. [Kernel proof of the uniform tail](../../NormalityChecker/QuantitativeStonehamTail.lean)

Fix a dyadic integer $X$ and any $0<T\le X$. Split $[X,X+T)$ at the **distinct** insertion positions strictly inside it. Include an insertion in the piece starting at its position. In each piece $[a_0,a_0+L)$, $R_{a_0+i}(x')=b^i R_{a_0}(x')$ for every $0\le i<L$. An insertion at $X+T$ contributes to the next interval. A one-point piece is admissible. For a degree-$a$ insertion with $X\le s(j)<2X$, some $m_iq_i^{j_i}$ lies in $[X/a,2X)$. That coordinate has at most $1+\lceil\log_{q_i}(2a)\rceil$ choices. Each of the other $a-1$ coordinates has $O(1+\log X)$ choices. The number $J$ of pieces is therefore $O((1+\log X)^{d-1})$, uniformly in the endpoint $X+T$. [Clean-prefix propagation](../../NormalityChecker/StonehamPolynomialExpansion.lean)

## Cancellation and the frequency gcd

Write $\mathrm e(z)=\exp(2\pi i z)$. Vandehey's Theorem 5.1 gives, for each integer $k\ge0$, positive computable $A_k,B_k$ depending on $k,b,S$. For every reduced $a/q$ with $q$ supported on $S$ and every $L\ge1$,

```math
\left|\sum_{i=0}^{L-1}\mathrm e(ab^i/q)\right|
\le (A_k q^{\alpha}L^{\gamma}+ B_k q^{-\alpha}L^{\nu})(1+\log q)^r .
```

Here $\alpha=1/(2^{k+2}-2)$, $r=2^{-k}$ and $\gamma=\gamma_k$, $\nu=\nu_k$ are specified below. The paper sums from 1 through $L$. Multiplication of $a$ by the inverse of $b$ modulo $q$ gives the displayed starting index. The bound applies also to pieces shorter than any specified power of $q$. We will sum its two terms as they stand. [Vandehey, preprint Theorem 5.1, pp. 13–14](https://arxiv.org/pdf/1606.07911#page=13) · [Published paper](https://doi.org/10.1007/s11854-019-0038-2)

At frequency $h\ge1$ the denominator on a piece starting with reduced denominator $Q$ is $q=Q/\gcd(h,Q)$. The upper-power term can use $Q^\alpha$. The inverse-power term pays the factor $\gcd(h,Q)^\alpha$. For every $H\ge1$ its harmonic sum obeys

```math
\sum_{h=1}^H\frac{\gcd(h,Q)^\alpha}{h}
\le (1+\log H)\sum_{r'\mid Q}(r')^{\alpha-1}
\le (1+\log H)\prod_{p'\in S}(1-(p')^{\alpha-1})^{-1}.
```

Group by $r'=\gcd(h,Q)$ and enlarge each class to all multiples $h=r'j$ up to $H$. The final product converges since $0<\alpha\le1/2$ and $S$ is finite. This bound holds separately for each $Q$ and for growing $H$. Treating the orbit estimate as uniform just for fixed $h$ would miss this loss. [Kernel finite gcd bound](../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean)

Apply the one-dimensional Erdős–Turán inequality in **unnormalized** form on $[X,X+T)$. Thus $T$ times the discrepancy is bounded by an absolute constant times $T/(H+1)+\sum_{h\le H}|S_h|/h$, where $S_h$ sums the phases on that interval. Replacing real values by rational prefixes costs at most $2\pi hKT/X$ in $S_h$, since $|\mathrm e(v)-\mathrm e(w)|\le2\pi|v-w|$. Its total contribution after harmonic weighting is $O(H)$. The rational part is a sum over the pieces. On a sufficiently late shell $Q\asymp X^d$ uniformly. Write the lengths as $L_j$ and use $\sum L_j=T$. For $0\le\gamma<1$, concavity gives $\sum_j L_j^\gamma\le J^{1-\gamma} X^\gamma$ (for $\gamma=0$ use $J$). For $\nu\ge1$, $\sum_j L_j^\nu\le X^\nu$. Together these give, for $1\le H\le X$ and the discrepancy $D_{X,T}$ of this piece of the real orbit,

```math
T D_{X,T}\ll X/H+H+
 (1+\log X)^{1+r}
 \left(J^{1-\gamma}X^{d\alpha+\gamma}+X^{-d\alpha+\nu}\right).
```

In particular the cost has the same bound for every final prefix $T$, even $T=1$. [Kernel finite transfer with the two external inequalities as hypotheses](../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean) · [Erdős–Turán in the interval convention, Bailey–Crandall, Theorem 2.2(9)](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf#page=4)

## Explicit exponents in every degree

Take $k=d-1$, set $a_k=1/(2^{k+2}-2)$, and use Vandehey's recurrence with $\gamma_0=0$, $\nu_0=1$,

```math
\gamma_{k+1}=\frac{1+\gamma_k+a_k\nu_k}{2(1+a_k)},
\qquad
\nu_{k+1}=\frac{1+\nu_k}{2}+\frac{(1+\gamma_k-\nu_k)a_k}{2(1+a_k)} .
```

Define $s_k=(1-\gamma_k)/a_k$ and $t_k=(\nu_k-1)/a_k$. Their difference is $4-2^{1-k}$ by $\gamma_k+\nu_k=2-2^{-k}$, and
$s_0=2$, $s_{k+1}=s_k+1-a_k t_k$. In particular $s_k\le k+2$ since $t_k\ge0$. Direct substitution gives $t_0=t_1=0$. For $j\ge2$ one has $t_j\le j-1$, so
$a_j t_j\le (j-1)/2^{j+1}$. The infinite sum of these last upper bounds, for $j\ge2$, is $1/2$. Every finite initial sum is strictly smaller. Thus

```math
s_k-(k+1)>1/2,\qquad (k+1)-t_k\ge1 .
```

The second inequality follows from the displayed difference and $s_k\le k+2$. This proves a strict margin on **both** terms in Vandehey's bound at the same differencing depth. [Lean margin for the rational recurrence](../../NormalityChecker/QuantitativeStonehamExponents.lean) · [Vandehey's recurrence and identity (15)](https://arxiv.org/pdf/1606.07911#page=14)

Take $H=\lfloor X^{\eta_d}\rfloor$ with

```math
\eta_d=\min\{1/2,\ 1-\gamma_k-da_k,\ 1-\nu_k+da_k\},
\qquad \ell_d=1+2^{-k}+(d-1)(1-\gamma_k).
```

The previous inequalities give $\eta_d>a_k/2=\delta_d$. Each shell-prefix count error is $O(X^{1-\eta_d}(1+\log X)^{\ell_d})$. Sum the errors for an arbitrary interval over complete dyadic shells and the last partial shell. The geometric series converges after dividing by its largest term since $1-\eta_d\ge1/2$. The finitely many initial positions, including $n=0$, cost $O(1)$ before normalization. Taking the supremum and dividing by $N$ gives $D_N\ll N^{-\eta_d}L_N^{\ell_d}$. Absorbing the logarithm into the strict margin yields the stated pure power. For the square $(a_1,\gamma_1,\nu_1)=(1/6,1/2,1)$, and for the cube $(a_2,\gamma_2,\nu_2)=(1/14,5/7,29/28)$. [Kernel all-prefix geometric summation](../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean)

## Effectivity and scope of verification

The precision used for the lower denominator bound is supplied in Lean by compactness. For fixed inputs it is **computable**. For increasing $L$ enumerate all upper subsets of $\{0,\ldots,L-1\}^d$ containing the anchor whenever it lies in the box. Start beyond every anchor coordinate. Check each weighted mass modulo $p^L$. Every admissible finite pattern extends to a global upper set containing the anchor by taking its upward closure. Conversely every global upper set restricts to one of these patterns. Points outside the box have weight at least $L$. The uniform-precision theorem therefore guarantees that the search halts. Passing at one precision implies passing at every larger one by reduction. The subsequent shell threshold, integer coefficient valuations, rational shift, support product, tail and counting constants all follow by finite operations. Vandehey's Theorem 5.1 gives the analytic constants recursively, and Erdős–Turán has an effective absolute constant from its trigonometric majorants. This yields an algorithm for $C$ even when enumeration is impractical. No ineffective Diophantine approximation constant enters. No numerical fit or precision search output is used as evidence for the asymptotic rate. [Uniform-precision theorem](../../NormalityChecker/StonehamPolynomialOrthant.lean) · [Explicit denominator threshold](../../NormalityChecker/StonehamPolynomialPrefix.lean) · [Vandehey's constants](https://arxiv.org/pdf/1606.07911#page=13)

At checkpoint `944e0c4` the Stoneham polynomial normality theorem is qualitative. The new Lean modules verify the real-tail estimate, the coefficient and frequency denominator arithmetic, the harmonic average of Vandehey’s two terms, the resulting finite discrepancy bound over arbitrary clean cuts, the rational recurrence margin and the final dyadic summation. The displayed asymptotic theorem for Stoneham values is a paper deduction. Vandehey and Erdős–Turán enter the Lean transfer as ordinary hypotheses. The assembly of the shell estimates, the fixed-support Euler product and the identification of the recurrence with Vandehey's exponents are given above. [Uniform real tail](../../NormalityChecker/QuantitativeStonehamTail.lean) · [Finite discrepancy statements](../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean) · [Exponent calculation](../../NormalityChecker/QuantitativeStonehamExponents.lean)

The three research modules build separately from the release umbrella. To replay them from this checkout, run

```sh
lake build NormalityChecker.QuantitativeStonehamTail NormalityChecker.QuantitativeStonehamDiscrepancy NormalityChecker.QuantitativeStonehamExponents
for module in QuantitativeStonehamTail QuantitativeStonehamDiscrepancy QuantitativeStonehamExponents; do
  lake env leanchecker "NormalityChecker.$module"
done
```

The public theorem axiom checks report only `propext`, `Classical.choice` and `Quot.sound`.

**A transfer when denominator slopes differ.** Suppose a separate arithmetic result supplies $X^\lambda\ll Q\ll X^D$ on all clean pieces of every late dyadic shell, for fixed $0<\lambda\le D$ and fixed prime support coprime to $b$. Suppose further that $J\ll(1+\log X)^A$ and the uniform real error is $O(X^{-\theta})$ with $\theta>0$. These hypotheses still give a power saving. Set $\beta=\tfrac12\min(1,\lambda,\theta)$, $H=\lfloor X^\beta\rfloor$. Pieces shorter than $X^{1/2}$ cost at most $J X^{1/2}$ positions. On the others $Q/\gcd(h,Q)\gg X^{\lambda-\beta}$ and $L\ge (Q/\gcd(h,Q))^{1/(3D)}$ for all sufficiently large $X$. Vandehey's Corollary 1.2 with $\varepsilon=1/(3D)$ saves a factor $O(X^{-\delta(\varepsilon)(\lambda-\beta)}(1+\log X))$ in each normalized rational sum. Erdős–Turán and the same summation give a pure saving of half the minimum of $\beta$, $1/2$, $\theta-\beta$ and $\delta(\varepsilon)(\lambda-\beta)$. Its constants are effective when the input bounds are effective. This version isolates what a new denominator calculation on another axis would supply. A lower bound on only a positive fraction of the shell, or merely $Q\to\infty$, does not verify these hypotheses. [Vandehey, Corollary 1.2 and its constructive proof in §6.1](https://arxiv.org/pdf/1606.07911#page=18)

For example, the earlier composite-axis argument treats a fixed $c>2$ coprime to $b$ when $b^{-c^j}$ converges to a unit in $\mathbb Z_p$ for some $p\mid c$. Its bounded loss at that prime gives $v_p(Q)=d v_p(c)\lfloor\log_c n\rfloor+O(1)$ for a degree-$d$ polynomial. The same pole comparison handles lower degrees. Thus the transfer applies with $D=d$ and $\lambda=d\log_c(p^{v_p(c)})$. This is a paper consequence of that composite denominator argument. It includes even $c>2$ by using $p=2$. At $c=2$ the leading square numerator vanishes on part of the scale. There one needs a separate lower denominator bound, and the general rate for odd-prime polynomials cannot be applied solely from the degree. [Earlier composite-axis argument and the parameter-two obstruction](../stoneham-powers-products.md#related-parameters-and-the-limit-of-the-argument)

## Historical comparison

Stoneham quantified digit-block frequencies in complete periodic expansions of rational fractions. For instance, his Theorem 3 gives an error parameter $2/\varphi(p^r)$ for the stated block lengths under a primitive-root hypothesis and $r>1$. His subsequent constructions pass from rational periods to normal numbers. In 1993 Kano gave quantitative estimates directly for radix orbits of lacunary numbers. With $A_n=1$, $\lambda_n=n$ and $\mu_n=c^n$, his unnormalized discrepancy estimate (13) already gives a power saving for the standard degree-one generator. The polynomial $f$ in Kano's Example 1 describes the spacing $\mu_n=f(\lambda_n)\beta^{\lambda_n}$. Here $P$ acts on the value of the series. [Stoneham, *On (j, ε)-normality in the rational fractions*, Theorem 3](https://matwbn.icm.edu.pl/ksiazki/aa/aa16/aa1631.pdf) · [Stoneham, 1973, pp. 282–284](https://doi.org/10.4064/aa-22-3-277-286) · [Kano, 1993, (13), Remark 2 and Example 1, pp. 914–915](https://doi.org/10.18910/10356)

Bailey and Crandall explicitly give $O(N^{-1/2}\log^2 N)$ for their perturbed rational orbit on the Stoneham schedule $m_i=c^i$, $n_i=i$, after Theorem 4.8. For the ordinary real orbit, discard the first $\lceil\sqrt N\rceil$ positions. The remaining points differ from the rational orbit by $O(N^{-1/2})$ in circle distance by the degree-one tail bound. Enlarging and shrinking each test interval by that distance transfers the same rate, with an additional $O(N^{-1/2})$ from the discarded positions. Bugeaud also records this rate for the real Stoneham orbit. The nonlinear estimate above uses the separate polynomial prefix theorem to handle collisions of ordered tuples and cancellation between degrees. The cited degree-one results do not establish the quadratic or cubic rates displayed here. Historical priority for those applications is unassessed beyond these comparisons. [Bailey–Crandall, *Random generators and normal numbers*, p. 535](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf#page=9) · [Bugeaud, *Distribution Modulo One and Diophantine Approximation*, §5.1](https://staff.dc.uba.ar/becher/aa/Bugeaud2012.pdf)
