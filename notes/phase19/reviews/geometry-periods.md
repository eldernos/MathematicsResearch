# Independent review of the Phase 19 geometry, sparse product and Taylor period notes

Scope: `notes/phase19/geometry.md`, `products-of-remainders.md` and `taylor-periods.md` as they stand uncommitted in the parent checkout `C:/Users/chaos/MathematicsResearch-phase19` (parent HEAD `b7bb042`). I re-derived every claim listed below by hand. The script [geometry-periods-check.py](geometry-periods-check.py) (standard library only, about 40 s) independently checks the finite statements in exact rational arithmetic and reproduces the tables quoted here. I used no subagents.

**Verdict.** I found no mathematical error in the three notes, and none in the Phase 18 results they cite (`translations.md` §§ "The exact worst-case change" and "Sparse signed integers", `programming.md` § B4, and the Lean file `NormalityChecker/SharpTranslation.lean`, whose statements I read). So there is no prior-phase error to report. I found one redundant hypothesis, two statements that could be sharpened, two places where the scope should be stated more plainly, two dangling links, and several precedents worth citing. Details follow, grouped by note.

Notation: $T z=bz \bmod 1$, $D_N$ is extreme discrepancy over half-open intervals, $d_N(x,y)=1-D_N(x-y)$, $F_b=(b-1)^{-1}\mathbb Z/\mathbb Z$, $M_N(w)=N^{-1}\sum_{n<N}\|b^nw\|$, $Z_0=\{w:M_N(w)\to0\}$ and $K_b=\{z:D_N(z)\to1\}$.

## geometry.md

### Finite distance (verified)

* **Maximum formula.** The formula $d_N(x,y)=\max_u|D_N(u+x)-D_N(u+y)|$ follows from `sharp_translation` at base point $u+y$ with $z=x-y$. Equality at $u=-y$ is `sharp_translation_zero`. A pointwise supremum of pseudometrics of the form $|f(u+x)-f(u+y)|$ is a translation-invariant pseudometric. When $N=1$, every single point has $D_1=1$. All of this is correct. The script checks it on 400 random exact cases (§1).
* **Concentration identity.** The identity $1-D=\inf_l\{1-Q(l)+l\}$ is exact. A useful precedent: $D_N$ over non-wrapping half-open intervals equals $\sup g-\inf g$ for $g(t)=F_N(t)-t$, so it is **Kuiper's statistic** $V_N=D_N^++D_N^-$ (Kuiper 1960; Kuipers–Niederreiter, *Uniform Distribution of Sequences*, Ch. 2 §1). Kuiper designed $V_N$ to be rotation invariant, and it equals the supremum of positive arc excess. That is precisely the note's complementation step. The script computes $D$ in Kuiper form and checks it against a brute-force arc infimum on random orbit samples.
* **Two-sided bound.** I checked the bound $\min(1/N,\|(b-1)z\|)\le d_N\le\frac{b^{N-1}-1}{b-1}\|(b-1)z\|$ and its proof (first pair for the lower bound, decomposition $z=h+u$ with $h\in F_b$ for the upper). Both are correct, and the script confirms them on random exact cases.
* **Zero set and topology.** The zero set is $F_b+\mathbb Z$, and the quotient topology is that of $\mathbb R/(b-1)^{-1}\mathbb Z$, because $d_N$ is squeezed between $\min(1/N,\cdot)$ and a Lipschitz multiple of the same quantity. This is correct.
* **Local formula.** The claim is $d_N=(b^{N-1}-1)|u|$ when this quantity is $<\min(1/2,1/N)$. When $L<1/2$, the minimal covering arc is the real segment from $h+u$ to $h+b^{N-1}u$, because the complementary covering arc has length $>1/2$. Any arc that misses a sample costs at least $1/N>L$. The formula is correct. The script checks it exactly on 300 random cases with $h\in F_b$.

### Asymptotic kernel (verified, one sharpening)

* **Kernel.** The decomposition $K_b=F_b+Z_0$ is correct. Here is an independent argument that avoids the connectedness of cluster sets used in Phase 18. Near-maximal arcs shrink and carry mass $\to1$. Comparing $n$ with $n+1$ on a density-one set forces their centres toward $F_b$, which is finite and separated. Changing $N$ by one moves mass by $O(1/N)$, so the nearest fixed point is eventually constant.
* **Digit form of $K_b$.** A reformulation not in the note may help readers. $K_b$ consists exactly of the numbers whose base-$b$ digits, at density-one positions, begin arbitrarily long runs of a single digit. Either the digit is a fixed $k\in\{1,\ldots,b-2\}$ (fixed point $k/(b-1)$), or each run is of $0$ or of $b-1$ (fixed point $0$). This holds because $0.kkk\ldots$ with $1\le k\le b-2$ stays a distance $\gg b^{-L}$ away from every $b$-adic rational with $L$ digits.
* **Topology remark: correct, could be sharper.** The sentence "its topology is different from the usual quotient topology" is correct. Since $K_b$ is dense, the usual quotient topology on $\mathbb R/K_b$ is **indiscrete**. Moreover $x\mapsto d^+(x,0)$ is constant on cosets of a dense subgroup and takes the values $0$ and $1$, so it is continuous at no point. The note's example ($x/b^j\to0$ with $d^+=1$) is one instance.

### Scalar ring $\mathbb Z[1/b]$ (verified)

* **Sufficiency.** $\mathbb Z$ acts by the subgroup property. Division by $b$ shifts the orbit by one index ($T^n(z/b)=T^{n-1}z$), so $|D_N(z/b)-D_N(z)|\le1/N$. Reduced $a/d$ with every prime of $d$ dividing $b$ lies in $\mathbb Z[1/b]$.
* **Necessity, with witness $1/(b-1)$.** The criterion "rational $\in K_b$ iff its denominator divides $b^j(b-1)$" is correct. Valuation count: if $p\mid d$ and $p\nmid b$, then $p\nmid a$, so $v_p$ of the denominator of $a/(d(b-1))$ equals $v_p(d)+v_p(b-1)>v_p(b-1)$.
* **Exhaustive check.** The script checks exhaustively that the orbit test agrees with the denominator test for $b\le12$, $q<120$. It also checks that $a/d$ preserves $K_b\cap\mathbb Q$ exactly when $d$ is $b$-primary, and that $1/(b-1)$ always witnesses failure ($b\le12$, $d<40$).
* **Scope.** The result concerns **rational** multipliers. Nothing is claimed about real $\lambda$ with $\lambda K_b\subseteq K_b$. The heading "Universal scalar ring" should say "rational scalar ring" or state this restriction.

### Single-residue test (verified; one hypothesis is redundant)

* **Reduction and test.** The Bézout reduction $(a/d)z\in K_b\iff z/d\in K_b$ is correct. So is the grid argument: the samples of $z/d$ lie within vanishing mean distance of the grid points $(c+(k_n\bmod d))/d$, which are $1/d$-separated.
* **Redundant clause.** The clause "and $(c+r)/d$ is fixed modulo one" follows from the density-one condition. Write $b^nz=c+k_n+e_n$. Then $k_{n+1}-bk_n-(b-1)c=be_n-e_{n+1}$ is an integer, so it vanishes whenever $|e_n|<1/(2b)$ and $|e_{n+1}|<1/2$. That happens on a density-one set of $n$. If $k_n\equiv r$ on a density-one set, then $(1-b)r\equiv(b-1)c \pmod d$, which says $d\mid(b-1)(c+r)$, that is, $(c+r)/d\in F_b$. So on good steps $k_n \bmod d$ follows the affine map $r\mapsto br+(b-1)c$, and the test reduces to "the residues spend asymptotically all their time at one fixed residue of this map". Keeping the clause is harmless, but the note should mention that it is automatic.
* **Numerical illustration (script §3; $b=10$, $c=1/3$, $d=3$).** $S$ is the set of squares. Take $z_1=1/3+\sum_{a\in S}(10^{-a}+10^{-a-1}+10^{-a-2})$, whose ones come in clumps of three, and $z_2=1/3+\sum_{a\in S}10^{-a}$. Since $10\equiv1\pmod 3$, $k_n\bmod3$ counts the ones seen so far. So residue $0$ has density one for $z_1$, while for $z_2$ each residue has density about $1/3$:

  | $N$ | $D_N(z_1)$ | $D_N(z_1/3)$ | $D_N(z_2)$ | $D_N(z_2/3)$ | density of $k_n\equiv0$ for $z_1$, $z_2$ |
  |---|---|---|---|---|---|
  | 1000 | 0.896 | 0.903 | 0.959 | 0.333 | 0.938, 0.341 |
  | 5000 | 0.947 | 0.954 | 0.976 | 0.332 | 0.972, 0.336 |
  | 20000 | 0.971 | 0.975 | 0.985 | 0.331 | 0.986, 0.333 |

  As predicted, $z_1/3\in K_{10}$, while $z_2/3$ has discrepancy near $1/3$, the value for three equally weighted grid points.
* **Overstatement.** "This resolves the rational-scaling question for the Phase 17 Lambert and sparse classes whenever their residue data are available" should read "reduces … to the residue-density computation". No Phase 17 class is actually decided here.

### Powers of the radix (verified)

* The equivalence of vanishing mean in bases $b$ and $b^h$ holds with explicit constants: $M^{(b^h)}_N\le hM^{(b)}_{hN}$ and $M^{(b)}_{hN}\le h^{-1}\big(\sum_{j<h}b^j\big)M^{(b^h)}_N$.
* The inclusion $K_b\subsetneq K_{b^h}$ holds, with witness $1/(b^h-1)$.
* $K_{a^r}\cap K_{a^s}=K_{a^{\gcd(r,s)}}$ is correct, because $Z_0\cap\mathbb Q=\mathbb Z[1/a]$ meets the points of order coprime to $a$ only in $\mathbb Z$. The script checks this identity on rationals ($a=2,3,5$; $r,s\le4$; $q<200$) and checks $1/4\in K_2\setminus K_3$.

### Integer multiplication (verified; sharpness is stronger than stated)

* **Two-sided bound.** I checked $\max(0,1-m(1-\alpha))\le D_N(mx)\le\min(1,m\alpha)$ and its proof (triangle inequality for the lower bound, the $m$-fold preimage for the upper). The script confirms it on 300 random exact cases. The local formula attains the factor $m$ in $d_N(mx,my)\le md_N(x,y)$.
* **Example $b=m+1$, $x=1/m^2$.** The identity $(m+1)^n\equiv1+nm\pmod{m^2}$ holds. When $m\mid N$, exact computation gives $D_N(x)=1/m$ and $D_N(mx)=1$ for $m=2,\ldots,8$.
* **Sharpening.** The note calls the factor $m$ sharp "across radices". The boundary spectrum proved two paragraphs later gives more. With $\theta=0$ it supplies, at **every fixed radix** and for every $m$ coprime to $b$, points with $D_N(mx)\to1$ and $D_N(x)\to1/m$. So the factor is asymptotically sharp at each fixed radix in that case. In general the sharp asymptotic factor is $m_0$, the part of $m$ coprime to $b$, consistent with $|D_N(b^jx)-D_N(x)|\le j/N$. The note should say so.

### Exact boundary spectrum $[1/m_0,1]$ (verified)

* **Necessity.** $m_0x=(mx)/m_b\in K_b$. The samples of $x$ then concentrate near the $m_0$ solutions of $m_0u\equiv c$. An interval inside a gap of length $1/m_0$ has vanishing mass, so $\liminf D_N(x)\ge1/m_0$. This is correct, including the case $m_0=1$.
* **Sufficiency.** The law $\theta\delta_0+(1-\theta)U_{m_0}$ is $T$-invariant, because $b$ permutes the grid $j/m_0$. Its discrepancy is exactly $\theta+(1-\theta)/m_0$. I checked every interval type: the excess at $0$, intervals containing $k$ grid points, and deficits on the gaps and on intervals that skip $0$. Multiplication by $m$ sends the whole grid to $0$, so it maps the limit law to $\delta_0$.
* **Construction.** The weighted cubic scheduler of Phase 18 B4 supplies $x$. The scalar continuity $D(\mu_i)\to D(\mu)$ under weak convergence, which handles the atoms here, is proved at the end of B4.
* **Simulation (script §6).** I scheduled the periodic digit words of the $b$-cycles of the grid, using the same greedy weight scheduler with linearly growing blocks:

  | $b$ | $m$ | $m_0$ | $\theta$ | $N$ | $D_N(x)$ | target | $D_N(mx)$ |
  |---|---|---|---|---|---|---|---|
  | 2 | 3 | 3 | 0 | 721140 | 0.3333 | 0.3333 | 0.9935 |
  | 2 | 3 | 3 | 0.5 | 721140 | 0.6638 | 0.6667 | 0.9935 |
  | 2 | 6 | 3 | 0.5 | 721140 | 0.6638 | 0.6667 | 0.9935 |
  | 3 | 4 | 4 | 0 | 721140 | 0.2500 | 0.2500 | 0.9953 |
  | 3 | 4 | 4 | 0.5 | 721140 | 0.6228 | 0.6250 | 0.9951 |
  | 10 | 21 | 7 | 0 | 720120 | 0.1438 | 0.1429 | 0.9990 |
  | 10 | 21 | 7 | 0.5 | 720628 | 0.5714 | 0.5714 | 0.9973 |

### Star and box counterexamples (verified exactly)

* **Star discrepancy** ($b=2$, $N=3$, $x=1/4$, $z=-1/256$). Exact values: $D^*(x)=1/2$, $D^*(x+z)=61/192=1/3-1/64$ and $D^*(z)=63/64$. The change $1/6+1/64$ exceeds $1-D^*(z)=1/64$, while the extreme discrepancy obeys the translation bound on the same data. Precedent: the Kolmogorov–Smirnov statistic is not rotation invariant, and that is why Kuiper introduced $V_N$.
* **Box discrepancy.** For the points $(1/3,1/3)$ and $(2/3,2/3)$, a brute-force search over boxes gives $8/9$. The largest empty box has area $4/9$, for example $[1/3+\epsilon,1)\times[0,2/3)$. Since $D(x)=D(z)=1$, even the inequality $|D(x+z)-D(x)|\le1-D(z)$ fails. The note's phrase "the finite maximum formula also fails" understates this slightly.

### Wasserstein remark (verified)

Couple the samples after a rotation by $c$, then use the rotation invariance of $W_1$ to Haar measure. The bound is correct.

### Editorial

The link `[Literature comparison](literature.md)` points to a file that does not exist in `notes/phase19/` of the parent checkout.

## products-of-remainders.md (verified, with precedent and a scope remark)

* **Moser–de Bruijn.** $A$ is the **Moser–de Bruijn sequence** (OEIS A000695; Moser 1962, de Bruijn 1964). The unique decomposition $n=a+2a'$ is its defining property. With $f(x)=\sum_{a\in A}x^a=\prod_{k\ge0}(1+x^{4^k})$, the identity $f(x)f(x^2)=1/(1-x)$ is classical. So $U=f(b^{-r})$, $V=f(b^{-2r})$ and $UV=b^r/(b^r-1)$. The script checks the decomposition for $n<2000$, and checks the product and the infinite-product form to $10^{-39}$ or better for $(b,r)=(2,2),(3,2),(2,3),(10,2)$.
* **Transcendence.** $f$ satisfies the Mahler equation $f(x)=(1+x)f(x^4)$ and is not rational. By Mahler's method (Mahler 1929; see Nishioka, *Mahler Functions and Transcendence*, 1996), $U$ and $V$ are expected to be **transcendental**, not merely irrational. I have not checked the exact theorem number, so this should be cited only after checking.
* **Rate.** $|D_N(x+U)-D_N(x)|\le1-D_N(U)=O(\log N/\sqrt N)$ follows from Phase 18's sparse-digit bound, since $A$ has counting function between $\sqrt{X/2}$ and $2\sqrt X$. The rate is **sharp** at $x=0$. An arc of length $l$ near $0$ misses about $\log_b(1/l)$ samples before each one-digit, and an arc away from $0$ misses the density-one cluster. So $1-D_N(U)\gg\min_l\{N^{-1/2}\log_b(1/l)+l\}\gg\log N/\sqrt N$. Numerically, for $b=2$, $r=2$ (script §7), $(1-D_N(U))\sqrt N/\log N$ equals $0.58, 0.49, 0.37, 0.49$ at $N=10^3,10^4,10^5,2\cdot10^5$. It oscillates boundedly with the Moser–de Bruijn counting function.
* **Product orbit.** The fractional part of $UV$ is $1/(b^r-1)$, with exact period $r$. Its cycle discrepancies are, for example, $2/3$ for $(2,2)$, $3/4$ for $(3,2)$, $4/7$ for $(2,3)$ and $10/11$ for $(10,2)$, all below one, as claimed.
* **Scope.** For $b\ge3$, $K_b$ is already not closed under multiplication on rationals: $(1/(b-1))^2\notin K_b$, as the script checks for $3\le b\le30$. The substantive content of the example is in base $2$, where $K_2\cap\mathbb Q=\mathbb Z[1/2]$ is a ring, and in every base for the mean-zero subgroup $Z_0$ (both $U-1$ and $V$ lie in $Z_0$), whose rational points $\mathbb Z[1/b]$ form a ring. The sentence "separates closure under multiplication …" should be stated for $Z_0$, or for $b=2$, to show what is new. The relevant literature precedent is Bergelson–Downarowicz (arXiv 2506.12929, Thm 8.1 and Cor 8.14), already cited in Phase 18. They construct deterministic numbers with a normal product in base 2. The present example concerns the much smaller class $Z_0$ and yields a rational product outside $K_b$. The note's closing caveat (no claim about a normal product inside the sparse class) is accurate.

## taylor-periods.md (verified; scope, numerics and precedents)

* **Counting lemma.**
  * At most $\min(d\log b/\log(cN),\,CN/d)\le\sqrt{CN\log b/\log(cN)}$ primes in $(cN,CN]$ have order $d$.
  * Summing over $d\mid R$ gives $H\le\tau(R)\sqrt{\cdot}$.
  * The elementary half of Wigert's bound, $\log\tau(R)\le(\log2+o(1))\log R/\log\log R$, is proved correctly. The $u^{1-\epsilon}$ split works because every exponent is at most $u/\log2$, and $a+1\le2^a$ applies to the large primes.
  * Combining these with $\log u\ge\log\log N-O(1)$ (from $\tau(R)\le R$) gives $\log R\ge(1/(2\log2)-o(1))\log N\log\log N$.
  * The variant with $\eta-1/2$ is also correct.
* **Application.** For an odd prime $p\in(N/2,N]$, $j=p$ is the only index with $p\mid j$, so $v_p(P_N)=-1$. The script confirms for $N\le3000$ that every odd prime in $(N/2,N]$ divides $q_N$ and that $H\le\tau(R)\sqrt{N\log2/\log(N/2)}$ holds. Deleting one axis, or $o(N/\log N)$ axes, keeps $H\gg N/\log N$, so the uniform deleted-axis version holds. The extensions to $\mathrm{Li}_s(1/b)$ hold by the same valuation argument: $v_p=-s$, and the primes dividing $b$ are eventually below $N/2$. The return-time remark holds for unit numerators, which is the case because the fraction is reduced. I did not re-verify the BBP and Bellard survival statements. The note correctly defers them to Phase 18 F5.
* **Numerics (script §8).** I computed $R=\mathrm{ord}_{q_N}(2)$ exactly. This is easy because every prime factor of $q_N$ is at most $N$. "Worst drop" removes the single axis that minimises the order:

  | $N$ | prime axes | $H$ | $\log R$ | $\log R/(\log N\log\log N)$ | same after worst drop | $\log R/N$ |
  |---|---|---|---|---|---|---|
  | 200 | 44 | 21 | 56.2 | 6.36 | 5.85 | 0.281 |
  | 800 | 137 | 61 | 200.6 | 15.80 | 15.33 | 0.251 |
  | 1600 | 250 | 112 | 349.1 | 23.68 | 23.23 | 0.218 |
  | 3000 | 428 | 191 | 614.5 | 36.90 | 36.46 | 0.205 |

  The proven constant $1/(2\log2)\approx0.72$ is correct but far from the observed behaviour. In the data, $\log\mathrm{ord}_{q_N}(2)$ grows roughly **linearly** in $N$ (ratio about $0.2$). The note should say that the theorem is a rigorous floor, not an estimate of the truth.
* **How far the method can go (precedent and scope).**
  * *Shape.* The bound has the same shape as the Erdős–Pomerance–Schmutz lower bound $\lambda(n)\ge(\log n)^{c\log\log\log n}$ for Carmichael's function (Acta Arith. 58, 1991), with $\log n\asymp N$. The order of $2$ can be much smaller than $\lambda$, however, so EPS does not imply the note's result. The note's dyadic-interval hypothesis is what makes an order bound possible.
  * *Lower side (sketch, not in the note).* The per-order count $N/d$ improves whenever most of the retained primes have large order. Baker–Harman (1996, Brun–Titchmarsh on average) give a positive proportion of primes with $P(p-1)>p^{0.677}$. Primes with $\mathrm{ord}_p(2)<N^{0.323}$ number $O(N^{0.646})$, because they divide $\prod_{d<N^{0.323}}(2^d-1)$. Together these would give $\log\tau(R)\ge(0.677-o(1))\log N$, hence the constant $0.677/\log2\approx0.98$. This assumes enough of those primes lie in $(N/2,N]$, a dyadic version I have not checked. Under GRH, $\mathrm{ord}_p(2)\ge p/f(p)$ for almost all $p$ (Erdős–Murty 1999) would give $1/\log2$, the limit of the divisor method.
  * *Upper side.* By shifted-smooth-prime results (Baker–Harman 1998, exponent $0.2961$, again in a dyadic version), some moduli satisfy the hypothesis "a positive proportion of the primes in $(N/2,N]$" and still have $\log\mathrm{ord}\le N^{0.30}$. Take the primes with $N^{0.2961}$-smooth $p-1$. Their orders divide the lcm of such $p-1$, whose logarithm is at most $\pi(N^{0.2961})\log N$. So no argument using only that hypothesis can prove the linear growth seen for $q_N$. Proving it would need arithmetic specific to the Taylor denominators.
* **Editorial.** The link `[Surviving grids](grids.md)` points to a file that does not exist in `notes/phase19/` of the parent checkout.

## Summary of requested items

| Item | Status |
|---|---|
| Rational scalar ring $\mathbb Z[1/b]$ of $K_b$ | Correct. State that it concerns rational multipliers. |
| Single-residue test | Correct. The fixed-point clause is implied by the density-one condition. "Resolves" should read "reduces to". |
| Finite pseudometric, zero set, local linearity | Correct. Exact checks pass. |
| Asymptotic pseudometric and quotient topology | Correct. The usual quotient topology is indiscrete, and $d^+(\cdot,0)$ is continuous at no point. |
| Integer multiplication bounds and boundary spectrum $[1/m_0,1]$ | Correct. The factor $m_0$ is asymptotically sharp at every fixed radix, which is stronger than "sharp across radices". |
| Star and box counterexamples | Correct, verified exactly ($61/192$, $63/64$, $8/9$). |
| Sparse product | Correct (Moser–de Bruijn). $U$ and $V$ are likely transcendental. The rate is sharp. State the novelty for $Z_0$ or for $b=2$. |
| $\liminf\log\mathrm{ord}/(\log N\log\log N)\ge1/(2\log2)$, uniformly after dropping an axis | Correct. The data show far faster (about linear) growth. The constant could improve to about $0.98$ (dyadic Baker–Harman, unchecked) or $1/\log2$ (GRH). Hypothesis-only arguments cannot reach linear growth. |
| Prior-phase errors | None found. |
