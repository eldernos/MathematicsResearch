# Review of Phase 18 tracks A and E: the principal family and its polynomial images

This is an independent adversarial review of the Phase 18 principal note and the algebra note. I re-derived every displayed estimate and every nonlinear step by hand. I also wrote a separate verification script without importing or copying the author's code. No stated theorem was found false. The objections below concern explicit constants, a lateness threshold that the proof uses but does not quantify, one citation-only claim and one missing corollary.

## Material reviewed

The files are untracked in the worktree of branch `t3/phase18-track-a-results` (base `dd8545b`). I reviewed this snapshot, taken on 2026-11-25:

| File | SHA-1 |
|---|---|
| `notes/phase18/principal.md` | `5e7b20ed098060b6052e694dfb4fdbb0edd38465` |
| `notes/phase18/algebra.md` | `bea3463c717f76b37a10e9c7ca62419670901a4d` |
| `scripts/phase18_principal.py` | `478bf3cb62d30a239b7344cba70b7746c36bbf59` |

The snapshot already contains the results the author reported in the coordinating thread:
- the quadratic theorem for $s\ge2$, with first-layer counts between $1$ and $p^2-1$;
- the precision-14 bound $<5.3\cdot10^{-7}$ for the flagship square;
- the affine correction $Y'$ on the second product axis.

Running `python -B scripts/phase18_principal.py` in the author's checkout passed every assertion.

The independent checks are in [`scripts/phase18_review_algebra.py`](../../../scripts/phase18_review_algebra.py). It differs from the author's script in method:
- it enumerates ordered loss pairs, without the author's symmetry multiplicity;
- it convolves directly modulo $p^L$, where the author updates fractions incrementally;
- on factorial plateaus it enumerates tuples directly and never uses the author's $F_l$ model;
- it cross-checks each certificate against a brute-force sweep over all pairs.

Run it with `python -B scripts/phase18_review_algebra.py --layers 21`. It takes about 35 seconds.

## Verdict by claim

| Claim | Status |
|---|---|
| A1. Every-prefix switch, $D_N\to1$ for $s=0$ and $D_N\to0$ for $s\ge1$ | Closed |
| A2. Exact reduced denominators $p^{sJ}$ and $b^{n_K}p^{sJ}$ | Closed |
| A3. Complete-period estimate, including the subgroup and lifting exponents | Closed, with constants made explicit (O4) |
| A4. Incomplete-period refinement through Gauss sums | Closed |
| A5. Power saving for every $s,d$ from Vandehey's Corollary 1.2 | Cited only, not verified (O2) |
| A6. Other schedules, Liouville property, Ridout, irrationality exponent | Closed |
| A7. Infinitely many raw denominator primes, lifting the exponent | Closed |
| E1. Rational affine combinations and joint normality | Closed |
| E2a. Top-residue congruence and the bound $1-\rho$, including $17/26$ and $27/40$ | Closed |
| E2b. Every rational polynomial of degree $r<d$ in $C(b,p,s,d)$ is normal when $s\ge r$ | Closed, lateness threshold to be stated (O1) |
| E2c. Flagship-square certificates at 14 and 21 layers | Closed, reproduced exactly by independent code |
| Universal normality for fast schedules, including factorial $P(X_{p,s})$ | Closed |
| Liouville property of factorial polynomial values | Closed |
| E3. Rectangle product, affine $Y'$ product, increasing-depth product | Closed (O3 is a hypothesis to restate) |

## A. Principal family

**A1. Every-prefix switch.** I checked the fixed-support criterion line by line.
- *Insertion blocks.* Blocks of length $T=\lfloor N^{\eta/2}\rfloor$ that contain an insertion cost at most $T(1+I(N))=O(N^{1-\eta/2})$.
- *Clean blocks.* On a block without insertions the exact identity $R_{a+j}=b^jR_a$ holds, so the denominator is constant because $(b,c)=1$.
- *Small denominators.* A clean block whose start has a small denominator consists entirely of small-denominator positions. Hypothesis 3 is therefore applied to positions, as it is stated.
- *Kernel range.* Any $d_0>2D/\eta$ gives $q_a\le(n+1)^D\le T^{d_0}$ eventually.
- *Lean statement.* The prose kernel statement matches `SmoothOrbitEstimate` and `fixed_support_orbit_estimate` in [SmoothOrbit.lean](../../../NormalityChecker/SmoothOrbit.lean#L16). That is the quantifier order, divisibility of the reduced denominator into a power of $c$, uniformity in $T$ with $q\le T^{d_0}$, and `phase` meaning $e^{2\pi i x}$. The four Lean files involved contain no `sorry`, `admit`, `axiom` or `native_decide`. I did not rebuild them, because no Lean toolchain is on the path in this environment.
- *Real tail.* With $H=\lceil(A+3)\log_b(2N)\rceil$ the tail bound $\ll(N+H+1)^Ab^{-H}=O(N^{-3})$ is correct.
- *The case $s=0$.* The tail is positive, so $\{b^nx\}\in(0,\epsilon)$ off a set of size $H\,I(N+H)$. This gives $D_N\ge1-\epsilon-o(1)$.

The principal application uses $I(N)\asymp N^{1/d}$, so $\eta=1-1/d$, together with the exact denominator from A2.

**A2. Exact denominators.**
- *The shifted prefix.* Every term of $p^{sJ}R_n$ is an integer, and modulo $p$ only the indices $mp^J$ with $1\le m<p$ survive. Each contributes $b^n$ because $t\mid n_i$, and there are between $1$ and $p-1$ of them.
- *The unshifted prefix.* At $n=n_K$ every earlier numerator term is divisible by each prime of $b$, while the newest term is a power of $p$.
- *Check.* The formula held at all 773 sampled cutoffs, at, before and after each insertion, for seven parameter sets. These include $s=0$, $t=1$ with $a=2$ (namely $b=10$, $p=3$) and $a=3$ (namely $b=26$, $p=3$).

**A3. Complete periods.** Put $a=v_p(b^t-1)$. Lifting the exponent gives $\operatorname{ord}_{p^e}(b)=tp^{e-a}$ for $e\ge a$.
- *Full inverse image.* The image of $\langle b\rangle$ modulo $p^a$ has $t$ elements. Its intersection with the kernel of reduction to $p^a$ has $tp^{e-a}/t=p^{e-a}$ elements, which is the whole kernel.
- *Grids.* Each coset $z(1+p^a\mathbb Z)$ is the progression of residues congruent to $z$ modulo $p^a$. One complete period is therefore $t$ grids of mesh $p^{a-e}$. Its unnormalized interval error is at most $t$, not merely $O(L/q)$.
- *Arbitrary length.* For $L$ steps the error is at most $t\lfloor L/T\rfloor+T\le p^aL/q+q$, so one may take $C_{b,p}=p^a$.
- *Segment sums.* With $q_k\in[(k/p)^s,k^s]$ and $L_k\ll k^{d-1}$, the two sums are $\ll K^{d-s}$ (because $d>s$) and $\ll K^{s+1}$. Dividing by $N\asymp K^d$ gives the first two terms.
- *Insertion term.* The buffer $H=\lceil2\log_b(2N)\rceil$ contributes $(1+\log N)N^{-(1-1/d)}$, and the circle enlargement costs $O(N^{-2})$.
- *Optimization.* The exponent $\min(s,d-1-s)/d$, maximized under $s\ge1$ and $d\ge s+2$, gives $\lfloor(d-1)/2\rfloor/d$ for fixed $d$ and $s/(2s+1)$ for fixed $s$.
- *Check.* I verified exactly, over 876 cases, the order formula, the full-inverse-image property, the bound $t$ for a full period and $p^aL/q+q$ for lengths from 1 to almost three periods. The cases cover eight pairs $(b,p)$, including $a=2,3$ and $p=7$. Numerically, $N^{1/3}D_N$ for the flagship real orbit is 5.98, 3.48, 5.53, 5.32 and 4.72 at $N=2^{10},2^{12},2^{14},2^{16},2^{18}$. This is consistent with $O(N^{-1/3})$. It is not evidence of the rate beyond that. The value $D_{1024}=0.593424$ agrees with the author's enclosure.

**A4. Incomplete periods.** I re-derived the Gauss-sum bound for imprimitive characters. Write $q=p^e$ and let $m=p^f u$ with $p\nmid u$ be the frequency.
- *Reduction.* Fibres of reduction to $p^{e-f}$ cancel unless $\Psi$ is trivial on the kernel. In that case the sum equals $p^f$ times a sum modulo $p^{e-f}$ at a unit frequency.
- *Plancherel.* That last sum has modulus at most $p^{(e-f)/2}$ by Plancherel, using equal moduli over unit frequencies. For the trivial character it is a Ramanujan sum of modulus at most 1. Hence $|\tau|\le\sqrt{q\gcd(m,q)}$.
- *Assembly.* The Fourier $\ell^1$ norm of the interval indicator on the time group is $O(\log T)$. Erdős–Turán with cutoff $q$ and the bound $\sum_{h\le q}\sqrt{(h,q)}/h\le(1+\log q)\sum_j p^{-j/2}$ complete the proof.
- *Check.* The bound held for every character and frequency modulo $3^{\le6}$, $5^{\le4}$, $7^{\le3}$ and $11^{\le2}$, 2403 frequency rows in all. The maximal ratio is exactly 1, so the bound is attained. Measured fragment errors stay below $0.18\sqrt q\log^2(2q)$.
- *Bookkeeping.* The exponents $(d-1-s/2)/d$, the condition $d>1+s/2$, $\log(2N)/N$ for $s\ge d$, and the balance $d=1+3s/2$ with limit $2/3$ are correct.

**A5. Vandehey comparison.** This paragraph depends entirely on the external quantitative Corollary 1.2. The repository's Lean theorem is explicitly qualitative and is proved by elementary differencing, so no quantitative input is kernel-checked. I did not verify the corollary's hypotheses: the admissible range of the length against the modulus, and uniformity in the numerator. See O2.

**A6. Other schedules and Diophantine properties.**
- *Sparse schedules.* $K(N)\ll N^{1-\eta}$ gives $q_n\le K(n)^s\le(n+1)^s$, and $q_n\to\infty$. Small denominators occur only before a fixed insertion.
- *Tail estimate.* The two-sided bound $(k+1)^{-s}b^{-n_{k+1}}\le X-U_k\le\frac b{b-1}b^{-n_{k+1}}$ is correct.
- *Liouville and Ridout.* The Liouville deduction for an infinite limsup is correct, and so is the Ridout deduction for a finite limsup above 1. Only the denominators $Q_k$ need to be $S$-units.
- *Irrationality exponent.* I redid $g\le\mu(X)\le\max\{g,1+g/(g-1)\}$, including the separation $|X-a/q|\ge1/(2qQ_k)$ when $a/q\ne U_k$ and the minimality bound on $n_k$. The threshold $g^2-3g+1\ge0$ is right. For non-integral $g$ a schedule such as $n_k=t\lfloor g^k\rfloor$ is meant.
- *Check.* Both tail bounds and the exact denominators $Q_k$ appear in the author's script for factorial and geometric schedules, and all passed.

**A7. Raw denominators.** The lifting-the-exponent formulas, for odd $\ell$ and for $\ell=2$ with odd $b$, held in 29541 cases. The argument from $\log|A_k|=o(h_k)$ is correct. Cancellation removes at most a divisor of $|A_k|$ from $H_b(h_k)$, and the part of $H_b(h)$ supported on a fixed finite set of primes is polynomial in $h$.

## E. Algebra

**E1. Linear combinations.**
- *Unique minimum.* The top order $s_*$ at $p$ gives $v_p(AR)=v_p(A)-s_*J$. Lower orders at $p$ lose $(s_*-s)J$, and the other primes and the constant are $p$-integral.
- *Rational coefficients.* After $b^vx=Y/D_0$, the reduced denominator is a multiple of $Q$, so depth only increases, and the support grows by the primes of $D_0$.
- *Joint normality.* It follows by applying the scalar result to every nonzero integer frequency vector. Linear independence of $1$ and the generators over $\mathbb Q$ follows because a rational number is not normal.
- See O5 for a wording nit.

**E2a. Top residue and the bound $1-\rho$.**
- *Congruence.* Tuples surviving at $p^{rsJ}$ have every $k_i=p^Ja_i$ with $a_i<p$, which is automatic since $u<p^d$. Their phases are $b^n$ modulo $p$, and lower degrees vanish for $J\ge1$. With $p\mid A$, the renormalization by $p^{rsJ-v_p(A)}$ is correct.
- *Passing density.* The lower density of passing positions is $\rho$.
- *Shape of the maximum.* The failure proportion increases on each failed cell, because its slope has the sign of $l-P\ge0$, and decreases elsewhere. Hence $1-\rho$ is the maximum over $y=1$ and the right ends of failed cells.
- *Examples.* For $(p,d,r)=(3,3,2)$ the counts 1, 3, 4 at 2, 9, 16 give $\rho=9/26$. For $(3,4,3)$ the counts 1, 4, 7, 8 at 3, 18, 33, 48 are all units, which gives $\rho=13/40$. Both are correct.

**E2b. Full normality when $s\ge r$.** This is the main new nonlinear claim. I re-proved the layer lemma: for $u\in[1,p^d)$ and $r<d$, the first nonempty loss layer satisfies $H\le r$ and $1\le C_H(u)<p^r$.
- *Least position of a layer.* $m_j=r-j+j/p^d$ is the least normalized position at layer $j\le r$. This follows from $p^{-dh}\ge1-h(1-p^{-d})$, the secant inequality for a convex function at integers.
- *A nonempty layer.* $m_r<1\le u$, so layer $r$ is always nonempty.
- *Shapes of losses.* For $H>0$, $u<m_{H-1}\le r$. With $2^d>r$ every zero-loss coordinate is $1$. At most $H-2$ positive-loss coordinates would give at least $r-H+2>m_{H-1}$. The losses are therefore either $H$ ones, or $H-2$ ones and a single two.
- *Counts.* The first shape has at most $\binom rH(p-1)^H$ tuples. The second has at most $(H-1)\binom r{H-1}(p-1)\le\binom r{H-1}(p-1)^{H-1}$, using $p\ge3$. Both are terms of $p^r=\sum_j\binom rj(p-1)^j$ other than the constant term.
- *From the lemma to the pole.* For late $J$, $p^{rsJ-sH}R_n(X^r)\equiv b^nC_H(u)\pmod{p^s}$, because later layers are divisible by $p^s$. Since $0<C_H<p^r\le p^s$, the depth is $rsJ-sH-v_p(C_H)-v_p(A)\ge rsJ-sr-(r-1)-v_p(A)$. Lower degrees have depth at most $(r-1)sJ$.
- *The criterion applies.* Sparsity is $\eta=1-r/d$, and there are no denominator exceptions at late cutoffs.

The checks support each step:
- *Brute force.* For $(p,d,r)=(3,3,2)$, $(3,4,2)$, $(3,4,3)$, $(5,3,2)$, $(5,4,3)$, $(7,3,2)$, $(3,5,4)$, $(3,5,2)$ and $(11,3,2)$, every cell of $[1,p^d)$ satisfies the lemma. In total there are about 39,000 cells.
- *Tightness.* The bound is attained: $C_H=8=3^2-1$ occurs for $p=3$, $r=2$. So $s\ge r$ cannot be weakened inside this argument.
- *Direct depths.* I computed the exact $p$-adic depth of the shifted prefix of $P(X)$ at every insertion event by direct convolution modulo $p^L$, through $K=243$ for $p=3$. The largest loss $rsJ-\text{depth}$ in each late shell is listed below.

| $(b,p,s,d)$ | $P$ | Allowed $sr+r-1+v_p(A)$ | Loss at late shells |
|---|---|---|---|
| $(2,3,2,3)$ | $z^2$ | 5 | 5, 5 at $J=3,4$ |
| $(2,3,2,3)$ | $3z^2+5z+1$ | 6 | 6, 6, 5 at $J=3,4,5$ |
| $(2,3,3,3)$ | $z^2$ | 7 | 7, 7 at $J=3,4$ |
| $(2,5,2,3)$ | $z^2$ | 5 | 4 at $J=2$ |
| $(8,3,2,3)$ | $7z^2-z+2$ | 5 | 5, 5, 4 at $J=3,4,5$ |
| $(2,3,3,4)$ | $z^3$ | 11 | 9 at $J=3$ |
| $(2,3,1,3)$, outside the theorem | $z^2$ | 3 | 7, 7, 9 at $J=2,3,4$, growing |

The bound is attained in late shells. At the early shell $J=2$ the loss for $C(2,3,2,3)^2$ is 6, above 5. This is consistent with the proof, which needs $b^{n_{k_i}}\equiv1\pmod{p^s}$, but it shows that the lateness qualifier does real work. See O1. The last row shows the flagship $s=1$ square losing depth, as expected where the theorem does not apply.

**E2c. Flagship-square certificates.** The sweep over refined precision is valid for every quadratic with nonzero rational leading coefficient:
- passing cells persist under refinement, because $M_L\equiv M_{L'}\pmod{p^{L'}}$;
- the leading coefficient's valuation and the linear term are dominated at late $J$.

My refinement code is written independently. It enumerates ordered loss pairs and solves the larger-loss coordinate by exact integer roots. It agrees with a brute-force sweep over all pairs at every precision from 1 to 9 layers. It reproduces the author's failed-cell histories and both exact fractions:

$$
\frac{10893289026421}{20594407551577180074}\approx5.289\cdot10^{-7}\quad(14\ \text{layers}),
$$

$$
\frac{14035285166320179631}{47872170047321719707829651794}\approx2.932\cdot10^{-10}\quad(21\ \text{layers}),
$$

with 13 and 22 failed cells respectively. These are rigorous upper bounds for $\limsup D_N$ of the flagship square. Normality of the flagship square remains open, as the note says.

**Universal normality for fast schedules.**
- *Plateau formula.* On plateaus the prefix is exactly $F_l(U,V)$. The discarded windows $[jn_k,jn_k+rn_{k-1}]$ have total length $O(n_{K-1}+K)=o(N)$.
- *Unequal pole orders.* When $J-v\to\infty$, the integer $k$ is not a power of $p$, so $v_p(U)=-sJ$ and $AU^r$ is the unique minimum.
- *Limit of the old prefix.* When $J-v$ is bounded, the limit $p^{sv}U\to B(m)$ in $\mathbb Q_p$ is correct. The layer counts are $m(p-1)p^{h-1}$, layer $h$ errors lie in $p^{s(H+1)}\mathbb Z_p$, and the geometric sum is $-m\lambda_s$. When $m>p$, the finite part has negative powers of $p$; it is still a fixed rational, and the argument is unaffected.
- *Real value of $B(m)$.* The identity $\sum_{a\le m}w(a)-m\lambda_s=\sum_h\delta_h\{m/p^h\}\in(0,1)$ holds, so $B(m)\in(-1,0)$.
- *Truncated binomial.* $\sum_{j\le l}\binom rjB^{r-j}$ is monic with integer coefficients, so its rational roots are integers. The case $l=r$ is $(B+1)^r$, which is nonzero because $B>-1$.
- *Compactness.* The final compactness argument is complete. The case $k=p^v$, that is $m=1$, falls in the bounded branch, which does not use the principal formula for $U$.
- *Checks.* I checked the identity exactly and the nonvanishing of the truncated binomial for $p=3,5,7$, $s=1,2,3$, $m<400$, $r\le6$ and all $l$, 75168 cases. The $p$-adic agreement of $p^{sv}U$ with $B(m)$ grows by about $s$ digits per unit of $v$, as the layer error predicts. Direct tuple enumeration on factorial plateaus, not using $F_l$, gives bounded losses: at most 1 for $z^2$ ($p=3$, $s=1$, $k\le90$), 2 for $z^2+3$ ($s=2$), 5 for $3z^3+z$ ($k\le30$) and 2 for $2z^2$ at $p=5$.

The Liouville property of $P(X_{p,s})$ for the factorial schedule is correct. Denominators are at most $DQ_k^r$, the map $P$ is Lipschitz near $X$, and the values $P(U_k)$ are infinitely many distinct rationals converging to a transcendental number.

**E3. Products.**
- *Rectangle construction.* It is correct. Two consecutive candidates differ by the factor $b^{-t_q}\not\equiv1\pmod p$. The prefix is a full rectangle outside $[m_j,m_j+m_{j-1})$, and that rectangle has $p$-depth exactly $s\lfloor\log_p\lceil j/2\rceil\rfloor$.
- *Affine product.* It is correct. Every nonempty prefix of $Y'$ is congruent to $b^{-m_1}$ modulo $p$, and the row formula keeps between $1$ and $p-1$ surviving rows. I verified the identity $Y'=(5/9)Y+(4/9)2^{-2}$ exactly on truncations. The exact depth $\lfloor\log_5K\rfloor$ held at every one of the 6832 insertion events through $n=2\cdot10^6$ for $X=C(2,5,1,3)$ and $Y=C(2,3,1,3)$.
- *Increasing-depth construction.* It held at all 2916 events through $4\cdot10^6$, with 43 rejected candidates exercising the second branch.
- *Scope.* The affine correction proves nothing about $XY$ itself, as the note states.

## Objections

**O1. State the lateness threshold in E2b and in the refined sweep.** The proof needs $b^{n_{k_i}}\equiv1\pmod{p^s}$ for $n_{k_i}=tp^{d(J-h_i)}a_i^d$ with $h_i\le r$. A sufficient condition is
$$
J\ge r+\left\lceil\frac{s-a}{d}\right\rceil,\qquad a=v_p(b^t-1).
$$
For the refined sweep at precision $p^L$, the condition is $J\ge h_*+\lceil(L-a)/d\rceil$. The direct computation above shows that the bound $sr+r-1+v_p(A)$ fails at $J=2$ and holds from $J=3$, exactly as this threshold predicts for $(b,p,s,d)=(2,3,2,3)$. Normality is unaffected, but the note should state the threshold.

**O2. Label the Vandehey power saving as conditional.** The power saving for every positive $s$ and $d\ge2$ rests on an external corollary whose hypotheses were not checked here. Neither the Lean theorem nor this review supports a quantitative rate. The comparison should say so, or give the exact statement used. A minor point: the block length exceeds $(q')^{\beta d/s}$, not only $(q')^{\beta d/(2s)}$.

**O3. Restate the hypothesis of the increasing-depth product.** That construction reuses the two-candidate test, so it needs $b^{t_q}\not\equiv1\pmod p$. The condition is stated only for the first construction. Divisibility $t_p\mid n_i$ is not needed there.

**O4. Give the explicit constants in A3.** One complete period has unnormalized error at most $t$, and one may take $C_{b,p}=p^a$. Stating this makes the complete-period bound fully explicit apart from the segment-sum constants.

**O5. Fix the wording "once $J>0$" in E1.** The valuation identity $v_p(AR)=v_p(A)-s_*J$ holds for every $J\ge0$. Large $J$ is needed only to make it a pole and the unique minimum.

**O6. Record a missing corollary.** Assume $s\ge r$ and $d>r$. Every nonzero integer frequency vector applied to $(X,X^2,\ldots,X^r)$ gives a nonconstant polynomial of degree at most $r$. E1 and E2b then show:
- $(X,\ldots,X^r)$ is jointly normal for $X=C(b,p,s,d)$;
- $X$ is not algebraic of degree at most $\min(s,d-1)$, since a rational value of a minimal polynomial is not normal.

The principal note currently says that the transcendence test "gives no decision" for $n_k=tk^d$. It should cross-reference this partial algebraic-degree exclusion. I verified the deduction but did not test it numerically.

## Scope not verified here

- The Lean commit `f1e4cec` (`NormalityChecker.RetirementDenominator`), reported in the coordinating thread, is not on this branch and was not reviewed.
- I did not rebuild any Lean file.
- The quantitative content of Vandehey's Corollary 1.2 is cited, not checked (O2).
- All numerical checks are finite. The asymptotic statements rest on the paper proofs re-derived above.
