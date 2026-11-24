# Exact discrepancy from simultaneous prime failures

Let $`b\ge2`$ be an integer, $`P`$ a finite set of primes, and $`J=\{p\in P:p\nmid b\}`$. Write $`M(P)`$ for the positive integers all of whose prime divisors lie in $`P`$, including 1. At integer order $`s\ge1`$ define the number and its shifted rational prefix by

```math
X_s=\sum_{m\in M(P)}\frac{1}{m^s b^m}.
```

```math
R_{s,n}=\sum_{m\in M(P),\,m\le n}\frac{b^{n-m}}{m^s}.
```

For $`N>0`$, $`D_N(X_s)`$ is the supremum over half-open intervals in $`[0,1)`$ of the absolute difference between interval length and empirical frequency among $`\{b^n X_s\}`$ for $`0\le n<N`$. Braces denote fractional part. Write $`D_\infty=\limsup_N D_N`$.

**Order-one theorem (kernel-verified).** At every $`p\in J`$ run the ordinary order-one test at precision $`L\ge1`$. Let $`E_{p,L}`$ be its failed integer positions and $`C(L)`$ the upper ordinary density of their intersection. Then

```math
D_\infty(X_1)=\lim_{L\to\infty} C(L).
```

In particular, vanishing limiting joint density is equivalent to base-$`b`$ normality. The empty intersection has density one, which gives maximal discrepancy when all support primes divide the radix. All upper densities use every integer cutoff. The theorem extends the one-prime formula to intersecting tests on different scales. [Formal theorem and finite loss bound](../NormalityChecker/JointPersistent.lean) · [One-prime theorem](persistent-discrepancy.md) · [Normality and interval frequencies](../NormalityChecker/BinaryDiscrepancy.lean)

## Deep cancellation and arbitrary cutoffs

For $`p\in J`$, set $`k=\lfloor\log_p n\rfloor`$ at $`n\ge1`$. Precision $`L`$ tests the normalized coordinate $`n/p^k`$ on a mesh of width $`p^{1-L}`$ in $`[1,p)`$. Let $`Z_{p,L}`$ be the union of the failing half-open cells and $`a_{p,L}=|Z_{p,L}|`$ its Lebesgue length. At scales $`k\ge L-1`$, the residue is that of $`p^k b^{-n}R_{1,n}`$ modulo $`p^L`$, a rational with denominator prime to $`p`$. Earlier positions may be ignored in a density. The checker omits them. The failed regions decrease to $`Z_p`$, of length $`a_p=\inf_L a_{p,L}`$. Call $`n`$ *deeply failed at $`p`$* when it fails at its own precision $`k+1`$. [Canonical residue at growing precision](../NormalityChecker/LocalizedCertificate.lean) · [Nesting](../NormalityChecker/DiscrepancyChecker.lean)

1. **Clear one prime.** Deep failure gives $`v_p(p^k b^{-n}R_{1,n})\ge k+1`$. Since $`p\nmid b`$, $`v_p(R_{1,n})\ge1`$. This removes $`p`$ from the reduced denominator even if other off-base primes are present and the latest insertion is recent. Do this separately for each $`p\in J`$, using that prime's own $`k`$.
2. **Clear the radix factors.** Take $`D=\lceil\log_2 N\rceil`$. For $`n<N`$, each base-prime part of $`m\le n`$ divides $`b^D`$. Outside the $`D`$ positions starting at each insertion $`m`$, every base factor in $`R_{1,n}`$ has therefore cleared. There are at most $`(D+1)^{|P|}`$ insertions by the exponent-vector count. A simultaneous deep failure outside these neighborhoods makes $`R_{1,n}`$ integral. The remaining positive tail satisfies $`0\le b^n X_1-R_{1,n}\le 1/(n+1)`$. Consequently, for each fixed $`0<\delta<1`$, all but $`o(N)`$ joint deep failures before $`N`$ give visits to $`[0,\delta)`$. [Independent and simultaneous clearing](../NormalityChecker/JointPersistent.lean) · [Insertion count](../NormalityChecker/LocalizedClearing.lean)
3. **Compare the counts.** On a whole $`p`$-scale $`p^j\le n<p^{j+1}`$, $`j\ge L-1`$, the fixed test fails at exactly $`p^j a_{p,L}`$ integers. Each coarse cell has that many integer positions per unit of normalized length. The deep count is exactly $`p^j a_{p,j+1}`$ by the unit mesh at that scale. Nesting bounds the number of fixed failures that pass deeply on any *part* of this scale by $`p^j(a_{p,L}-a_p)`$. If $`p^k\le N<p^{k+1}`$, the sum of the $`p^j`$ up to $`k`$ is at most $`pN/(p-1)\le2N`$. Thus the joint fixed count $`F_L(N)`$ and joint deep count $`G(N)`$ satisfy

```math
F_L(N)\le G(N)+2N\sum_{p\in J}(a_{p,L}-a_p).
```

   Indeed, each fixed failure omitted from the deep intersection belongs to at least one individual difference. This bound also holds for the checker's early-position convention. A genuinely deep failure past all the initial scales also fails every fixed test at that precision. The comparison uses individual widths even when the geometric scales have very different endpoints. [Kernel proof of the uniform loss estimate](../NormalityChecker/JointPersistent.lean)

4. **Take the limits.** The existing joint soundness theorem gives $`D_\infty(X_1)\le C(L)`$. By step 2, $`G(N)/N\le D_N(X_1)+\delta+o(1)`$, using the anchored interval. Step 3 gives the reverse limiting inequality after $`N\to\infty`$, $`L\to\infty`$ and $`\delta\downarrow0`$. In particular, $`\limsup_N G(N)/N`$ has the same value. Counting the integer mesh at each finite depth allows arbitrary measurable limiting regions. [Joint upper bound](../NormalityChecker/DiscrepancyChecker.lean) · [Equality](../NormalityChecker/JointPersistent.lean)

## The compact set of attainable phases (paper proof)

The maximum-on-closure and all-prefix statements now also have kernel proofs. [Formalization](higher-order-joint.md)

Use the circle $`\mathbb T=\mathbb R/\mathbb Z`$, $`\alpha_p=1/\log p`$ (natural logarithm), and $`H=\overline{\{t\alpha\bmod1:t\in\mathbb R\}}\subseteq\mathbb T^J`$. For a family $`B=(B_p)_{p\in J}`$ of measurable subsets of $`[1,p)`$, let $`\{z\}`$ denote fractional part and put

```math
Q_B(\theta)=\int_0^1\prod_{p\in J}
{\bf1}_{B_p}\!\left(p^{\{\theta_p+\log_p u\}}\right)\,du.
```

Then $`C(L)=\max_H Q_{Z_L}`$, and $`D_\infty(X_1)=\max_H Q_Z`$. These maxima weight all past scales by their ordinary lengths. For two independent scales the product of average densities instead computes their joint logarithmic density.

For a fixed finite mesh, replace the integer count by length on $`(0,N)`$. Beyond the finitely many early scales every boundary is integral, so the replacement costs $`O_{P,L}(1)`$. Substitution $`y=Nu`$ gives precisely $`NQ_{Z_L}(\alpha\log N)`$. The finite-mesh score is continuous on the torus by dominated convergence. For a given phase, the countably many $`u`$ hitting an endpoint have measure zero. The tail closure of $`\alpha\log N`$ is $`H`$. Indeed, compactness supplies arbitrarily large return times of the real flow arbitrarily close to zero (take differences in a convergent subsequence at increasingly separated positive times). Hence every real orbit point is approached at unbounded positive times $`t`$, and replacing $`e^t`$ by its nearest integer changes the log phase by $`o(1)`$. Every maximizing phase can therefore be approached by integer cutoffs.

For each coordinate the integral of an indicator of a set $`B_p`$ is at most $`p|B_p|/(p-1)`$ uniformly in $`\theta_p`$. To see this, choose $`T=p^{\{\theta_p\}}\in[1,p)`$, set $`x=Tu`$, and sum lengths of the sets $`p^{-j}B_p`$ for $`j\ge0`$ in $`(0,T)`$, dividing by $`T`$. The product-indicator difference for nested families is bounded by the sum of the individual differences. Thus $`Q_{Z_L}\to Q_Z`$ uniformly, so $`Q_Z`$ is continuous and maxima converge. The same comparison applies to any decreasing finite-mesh approximations below.

With Haar probability on $`H`$, invariance and Fubini give $`\int_H Q_Z=\mu_H(H\cap\prod_{p\in J}\log_p Z_p)`$, where $`\log_p Z_p`$ is taken modulo one. The nonnegative continuous score vanishes everywhere exactly when this Haar mass is zero. For two distinct primes $`p,q`$, their log ratio is irrational by unique factorization, so $`H=\mathbb T^2`$. In that case normality is equivalent to at least one of $`|Z_p|,|Z_q|`$ vanishing. For three or more primes the formula uses $`H`$ itself. Distinct prime factors alone do not prove rational independence of the **reciprocals** of their logarithms. [Two-prime calculations and logarithmic density](overlapping-certificates.md)

## Higher orders and the lower-order residues (paper proof)

The all-orders result is now formalized by finite principal-unit expansions. [Lean proof and scope](higher-order-joint.md)

At $`s>1`$ the ordinary deepest test only forces $`v_p(R_{s,n})\ge k+1-sk`$. A clean counterexample has $`s=2,\ b=36,\ P=\{2,3,7\},\ n=186`$. Here $`k=2`$, the order-two test vanishes modulo $`7^3`$, the last insertion was at 168, and the reduced denominator is exactly 7. Lean verifies all these finite assertions. This refutes the proposed one-step clearing implication. The Phase 11 nullity theorem implies that the limiting single-order test is also exact for unsigned full supports, even though this particular finite local clearing implication fails. [Kernel counterexample](../NormalityChecker/JointPersistent.lean)

There is an unconditional replacement. Define $`Z_{p,d}`$ in this section to be the *persistent* failed set for order $`d`$, and set $`B_p=\bigcap_{d=1}^s Z_{p,d}`$. Then

```math
D_N(X_s)-Q_B(\alpha\log N)\longrightarrow0.
```

```math
D_\infty(X_s)=\max_{\theta\in H}Q_B(\theta).
```

Equivalently, take the limiting upper ordinary density of simultaneous failures for **all** pairs $`(p,d)`$, $`p\in J,\ 1\le d\le s`$, at common precision $`L\to\infty`$. For $`2\in J`$, the first cell for $`p=2`$ passes on the entire scale at every order and $`X_s`$ is already known to be normal. For $`J=\varnothing`$, the positive tail and clearing delay $`s\lceil\log_2 N\rceil`$ give $`D_N\to1`$. We may therefore treat odd off-base primes. [Prime-two and all-base conclusions](../NormalityChecker/MaximalSupport.lean)

**The local identity.** Take the Teichmüller unit $`w\in\mathbb Z_p^\times`$ lifting $`b^{-1}\bmod p`$, so $`w^p=w`$. Put $`\lambda=\log_p(b^{-1}/w)`$, using the *$`p`$-adic logarithm* here only. It is nonzero and belongs to $`p\mathbb Z_p`$. Indeed, logarithm and exponential are inverse on $`1+p\mathbb Z_p`$ and $`p\mathbb Z_p`$, and $`b^{p-1}>1`$. Write $`S_p=M(P\setminus\{p\})`$. For $`1\le d\le s`$ and $`1\le t<p`$ define

```math
U_{p,d}(t)=\sum_{i\ge0}p^{id}
 \sum_{r\in S_p,\,r\le p^it}\frac{w^r}{r^d}.
```

Every row has $`p`$-adic valuation at least $`id`$, so convergence is uniform. Reduction modulo $`p^L`$ is exactly the finite residue test. Rows with $`id\ge L`$ disappear, and the canonical lift $`(b^{-1})^{p^{L-1}}\bmod p^L`$ equals $`w\bmod p^L`$ by the principal-unit congruence. Hence $`Z_{p,d}=\{t:U_{p,d}(t)=0\}`$ and all these sets are measurable.

For any real $`y\in[n,n+1)`$, $`n\ge1`$, put $`k=\lfloor\log_p y\rfloor,\ t=y/p^k`$. Write $`c_h=\lambda^h/h!`$. In $`\mathbb Q_p/\mathbb Z_p`$ we have

```math
 b^{-n}R_{s,n}\equiv
 \sum_{d=1}^s c_{s-d}\,p^{-kd} U_{p,d}(t)
 \pmod{\mathbb Z_p}.
```

Indeed $`b^{-m}=w^m\exp(\lambda m)`$. In $`b^{-m}/m^s`$, the exponential terms of degree $`h\ge s`$ are integral since $`c_h\in\mathbb Z_p`$. At $`h=s-d`$, split $`m=p^{k-i}r`$. Then $`w^m=w^r`$, and $`m\le n`$ is equivalent to $`r\le p^i t`$. This gives the displayed sum through $`i=k`$. Extending to $`i>k`$ adds only integral rows even after multiplication by $`p^{-kd}`$. In particular this identity holds for **every real point in the unit interval belonging to one digit position**.

**From the identity to the discrepancy.** If $`t\in B_p`$, the identity clears $`p`$. Otherwise let $`d`$ be the largest order with $`U_{p,d}(t)\ne0`$. Fix $`L`$ and discard points for which *any* nonzero $`U_{p,h}`$ has valuation at least $`L`$. For the remaining points, write $`A=\max_{h<s} v_p(c_h)`$, taking $`h=0,\ldots,s-1`$. The $`d`$-th summand has valuation at most $`A+L-1-kd`$. All smaller orders have valuation at least $`-k(d-1)`$. For $`k>A+L`$ the $`d`$-th summand therefore determines the valuation and the reduced denominator retains at least $`p^{k-A-L}`$. The discarded sets for each $`p,h`$ decrease to the empty set as $`L\to\infty`$. The preceding one-coordinate length bound makes their share in every real prefix $`(0,N)`$ tend to zero uniformly in $`N`$ as $`L`$ grows. A fixed initial segment handles the requirement that all $`k`$ be large.

Here are the bounds at an arbitrary cutoff $`N`$. The real points $`0<y<N`$ whose normalized phases lie in all the $`B_p`$ have length $`NQ_B(\alpha\log N)`$. Every unit interval meeting this set gives an integral prefix after the base factors have cleared, apart from early positions. The positive tail is at most $`1/(n+1)^s`$, so $`[0,\delta)`$ gives $`D_N\ge Q_B(\alpha\log N)-\delta-o(1)`$. For the reverse bound, take the existing clean blocks of length $`2^{\lfloor\log_4 N\rfloor}`$. The initial, recent-insertion, and incomplete blocks comprise $`o(N)`$ positions. If a remaining block contains a real point outside the joint persistent set and the discarded sets, some prime has the growing denominator just proved. That denominator divides the starting denominator, which is supported on the fixed off-base primes and polynomially bounded in block length. The uniform short-orbit estimate gives error at most $`\eta`$ per position for every interval, once the block starts sufficiently late. The other blocks occupy at most the length of the joint persistent set plus the discarded length. Take the limsup at fixed $`L,\eta,\delta`$, then let the three errors vanish. The uniform approximation by finite levels and the compact phase argument give the stated maximum. [Clean-block bounds](../NormalityChecker/SupportDiscrepancy.lean) · [Uniform transfer and block size](../NormalityChecker/WeightedBlocks.lean)

## What finite refinement can detect

**Two generators (paper deduction).** If $`P=\{p,q\}`$ and $`p\nmid b`$, $`Z_{p,d}`$ has only finitely many points for every $`d\ge1`$. For odd $`p`$, partition $`[1,p)`$ into finitely many intervals with endpoint ratio strictly less than $`q`$. Given $`t_1<t_2`$ in one interval, there exists an $`i\ge0`$ with a power of $`q`$ in $`(p^it_1,p^it_2]`$ because $`a\log_p q\bmod1`$ is dense. Choose the first such $`i`$. At this row exactly one summand changes since $`t_2/t_1<q`$. Its valuation is $`id`$, and every later change has larger valuation. Thus $`U_{p,d}(t_1)\ne U_{p,d}(t_2)`$. Each partition interval has at most one zero. The prime-two case has none. This gives a refinement proof of normality for the whole mixed-pair family at every order. For example $`b=32,\ P=\{2,31\}`$ has a failed interval $`[16,31)`$ at the first precision. The existing mixed-pair argument also gives quantitative estimates. For context, the localized-logarithm manuscript treats the binary pair $`\{2,3\}`$ and other families, while Vandehey gives fixed-prime-support short-orbit estimates. [Mixed-pair theorem and literature](mixed-localized-logarithms.md) · [Vandehey, Corollary 1.2](https://arxiv.org/abs/1606.07911)

More generally, for any nonempty cofactor support the normalized thresholds $`r/p^i`$ are dense because they include the powers of any one cofactor prime. An interior threshold has a unique representation with $`p\nmid r`$. On a small neighborhood avoiding all other thresholds in rows through $`i`$, its jump modulo $`p^{id+1}`$ is nonzero. Thus no $`Z_{p,d}`$ contains an open interval. This does not bound the measure of a general $`Z_{p,d}`$. Phase 11 proves that every off-base failed region has measure zero, precluding positive persistent mass. Finding a fixed unsigned support with failures at every finite depth is still a separate problem. [Nullity and finite termination](unsigned-finite-support.md)

**A joint refinement example (finite exact computation).** For $`b=78,\ P=\{2,3,5,7\}`$, the two off-base primes both retain positive-length failed intervals through precision three. At each of those precisions the joint upper density is positive by the two-prime phase formula. At precision four the 5-test certifies normality. Exact widths from the checker are

| Precision | Failed width for 5 | Failed width for 7 |
| ---: | ---: | ---: |
| 1 | 1 | 1 |
| 2 | 2/5 | 3/7 |
| 3 | 6/25 | 6/49 |
| 4 | 0 | 6/49 |

**Arbitrarily deep finite failures (paper construction).** For every $`L`$ there is a finite support with a single off-base prime 3 for which the precision-$`L`$ failed set contains a neighborhood of $`t=5/2`$. Allow the support and radix to vary. Begin with cofactor 2 and require $`b\equiv1\bmod3`$, so $`w=1`$. The top row at $`t`$ is $`1+1/2=0\bmod3`$. After attaining zero modulo $`3^j`$, put $`Y=t3^j`$. Choose two distinct primes in $`(Y/2,Y]`$. For $`j=1`$ use 5 and 7. For $`j\ge2`$ the second Ramanujan prime $`R_2=11`$ guarantees both. Each new prime $`q`$ is larger than every previous row's cutoff, and its only multiple at most $`Y`$ is itself. Including it therefore adds $`3^j/q`$ modulo $`3^{j+1}`$. The subset sums of any two nonzero elements of $`\mathbb F_3`$ cover that field, so a subset of the two primes cancels the next digit. Iterate $`L-1`$ times and take the radix to be the square of the product of the chosen cofactor primes (including 2). None divides 3 and all divide the radix. The half-integer cutoff $`t3^i`$ never hits a threshold, so the finite zero at $`t`$ lasts on an open neighborhood. The construction yields no positive lower bound uniform in $`L`$ for a fixed support. [Ramanujan's interval theorem](https://arxiv.org/abs/0907.5232)

For a worked instance take cofactors $`2,17,41,103,311,929`$ and radix $`82\,967\,135\,716`$, a multiple of all six congruent to 1 modulo 3. The fixed support obtained by adjoining 3 passes for the first time at precision **12**. Its exact certificate upper bounds at precisions 9, 10, 11 and 12 are $`1569/32768,\ 1569/32768,\ 1937/49152,\ 0`$. Nesting and the strictly positive bound at precision 11 rule out every earlier zero certificate for this support. Both tables are reproducible with the rational checker. [Exact checker](../scripts/localized_certificate.py)

```sh
python3 scripts/localized_certificate.py 78 5 4 2 3 5 7
python3 scripts/localized_certificate.py 78 7 4 2 3 5 7
python3 scripts/localized_certificate.py 82967135716 3 12 2 3 17 41 103 311 929
```
